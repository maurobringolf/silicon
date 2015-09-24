/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import java.io._
import java.nio.file.Path

import org.apache.commons.io.FileUtils
import org.slf4s.Logging
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Unknown, Unsat, Sat, Prover}
import viper.silicon.reporting.{ProverInteractionFailed, Bookkeeper}
import viper.silicon.state.terms._
import viper.silicon.utils.Counter

/* TODO: Pass a logger, don't open an own file to log to. */
abstract class ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends Prover with Logging {
  val termConverter = new TermToSMTLib2Converter(bookkeeper)
  import termConverter._

  protected var proverName :String = _
  protected var startupArgs :List[String] = _
  protected var pushPopScopeDepth = 0
  protected var isLoggingCommentsEnabled: Boolean = true
  protected var logFile: PrintWriter = _
  protected var process: Process = _
  protected var input: BufferedReader = _
  protected var output: PrintWriter = _
  protected var proverPath: Path = _
  protected var logPath: Path = _
  protected var counter: Counter = _
  protected var lastTimeout: Int = 0

  protected def createInstance() = {
    log.info(s"Starting $proverName at ${proverPath}")

    val userProvidedArgs: List[String] = config.proverArgs.get match {
      case None =>
        List()

      case Some(args) =>
        log.info(s"Additional command-line arguments are $args")
        args.split(' ').map(_.trim).toList
    }
    val builder = new ProcessBuilder(proverPath.toFile.getPath :: startupArgs ::: userProvidedArgs :_*)
    builder.redirectErrorStream(true)

    val process = builder.start()

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        process.destroy()
      }
    })

    process
  }



  def path() = proverPath

  def version(): Version = {
    val versionPattern = """\(?\s*:version\s+"(.*?)"\)?""".r
    var line = ""

    writeLine("(get-info :version)")

    line = input.readLine()
    logComment(line)

    line match {
      case versionPattern(v) => Version(v)
      case _ => throw new ProverInteractionFailed(s"Unexpected output of Z3 while getting version: $line")
    }
  }

  /* Note: This is just a hack to get the input file name to the prover */
  def proverRunStarts() {
    logComment(s"Input file is ${config.inputFile.getOrElse("<unknown>")}")
  }

  def start() {
    counter = new Counter()
    logPath = config.proverLogFile
    logFile = silver.utility.Common.PrintWriter(logPath.toFile)
    process = createInstance()
    input = new BufferedReader(new InputStreamReader(process.getInputStream))
    output = new PrintWriter(new BufferedWriter(new OutputStreamWriter(process.getOutputStream)), true)
  }

  def reset() {
    stop()
    counter.reset()
    pushPopScopeDepth = 0
    lastTimeout = 0
    start()
  }

  def stop() {
    this.synchronized {
      logFile.flush()
      output.flush()

      logFile.close()
      input.close()
      output.close()

      process.destroy()
      //      z3.waitFor() /* Makes the current thread wait until the process has been shut down */

      val currentLogPath = config.proverLogFile
      if (logPath != currentLogPath) {
        /* This is a hack to make it possible to name the SMTLIB logfile after
         * the input file that was verified. Currently, Silicon starts Z3 before
         * the input file name is known, which is partially due to our crappy
         * and complicated way of how command-line arguments are parsed and
         * how Silver programs are passed to verifiers.
         */

        FileUtils.moveFile(logPath.toFile, currentLogPath.toFile)
      }
    }
  }

  def push(n: Int = 1) {
    pushPopScopeDepth += n
    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + pushPopScopeDepth
    writeLine(cmd)
    readSuccess()
  }

  def pop(n: Int = 1) {
    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + pushPopScopeDepth
    pushPopScopeDepth -= n
    writeLine(cmd)
    readSuccess()
  }

  private val quantificationLogger = bookkeeper.logfiles("quantification-problems")

  def assume(term: Term) = {
    /* Detect certain simple problems with quantifiers.
     * Note that the current checks don't take in account whether or not a
     * quantification occurs in positive or negative position.
     */
    term.deepCollect{case q: Quantification => q}.foreach(q => {
      val problems = state.utils.detectQuantificationProblems(q)

      if (problems.nonEmpty) {
        quantificationLogger.println(s"\n\n${q.toString(true)}")
        quantificationLogger.println("Problems:")
        problems.foreach(p => quantificationLogger.println(s"  $p"))
      }
    })

    assume(convert(term))
  }

  def check(timeout: Int = 0) = {
    setTimeout(timeout)

    writeLine("(check-sat)")

    readLine() match {
      case "sat" => Sat
      case "unsat" => Unsat
      case "unknown" => Unknown
    }
  }

  def assume(term: String) {
    bookkeeper.assumptionCounter += 1

    writeLine("(assert " + term + ")")
    readSuccess()
  }

  def assert(goal: Term, timeout: Int = 0) = assert(convert(goal), timeout)

  def assert(goal: String, timeout: Int) = {
    bookkeeper.assertionCounter += 1

    setTimeout(timeout)

    val (result, duration) = config.assertionMode() match {
      case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal)
      case Config.AssertionMode.PushPop => assertUsingPushPop(goal)
    }

    logComment(s"${common.format.formatMillisReadably(duration)}")
    logComment("(get-info :all-statistics)")

    result
  }

  private def assertUsingPushPop(goal: String): (Boolean, Long) = {
    push()

    writeLine("(assert (not " + goal + "))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine("(check-sat)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    pop()

    (result, endTime - startTime)
  }

  private def assertUsingSoftConstraints(goal: String): (Boolean, Long) = {
    val guard = fresh("grd", sorts.Bool)

    writeLine(s"(assert (implies $guard (not $goal)))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine(s"(check-sat $guard)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    (result, endTime - startTime)
  }

  def write(content: String) {
    writeLine(content)
    readSuccess()
  }

  def statistics(): Map[String, String]= {
    var repeat = true
    var line = ""
    var stats = scala.collection.immutable.SortedMap[String, String]()
    val entryPattern = """\(?\s*:([A-za-z\-]+)\s+((?:\d+\.)?\d+)\)?""".r

    writeLine("(get-info :all-statistics)")

    do {
      line = input.readLine()
      logComment(line)

      /* Check that the first line starts with "(:". */
      if (line.isEmpty && !line.startsWith("(:"))
        throw new ProverInteractionFailed(s"Unexpected output of $proverName while reading statistics: $line")

      line match {
        case entryPattern(entryName, entryNumber) =>
          stats = stats + (entryName -> entryNumber)
        case _ =>
      }

      repeat = !line.endsWith(")")
    } while (repeat)

    toMap(stats)
  }

  def enableLoggingComments(enabled: Boolean) = isLoggingCommentsEnabled = enabled

  def logComment(str: String) =
    if (isLoggingCommentsEnabled) {
      val sanitisedStr =
        str.replaceAll("\r", "")
          .replaceAll("\n", "\n; ")

      logToFile("; " + sanitisedStr)
    }

  private def freshId(prefix: String) = prefix + "@" + counter.next()

  /* TODO: Could we decouple fresh from Var, e.g. return the used freshId, without
   *       losing conciseness at call-site?
   *       It is also slightly fishy that fresh returns a Var although it
   *       declared a new Function.
   */
  def fresh(idPrefix: String, sort: Sort) = {
    val id = freshId(idPrefix)

    val decl = sort match {
      case arrow: sorts.Arrow => FunctionDecl(Function(id, arrow))
      case _ => VarDecl(Var(id, sort))
    }

    write(convert(decl))

    Var(id, sort)
  }

  def sanitizeSymbol(symbol: String) = termConverter.sanitizeSymbol(symbol)

  def declare(decl: Decl) {
    val str = convert(decl)
    write(str)
  }

  def resetAssertionCounter() { bookkeeper.assertionCounter = 0 }
  def resetAssumptionCounter() { bookkeeper.assumptionCounter = 0 }

  def resetCounters() {
    resetAssertionCounter()
    resetAssumptionCounter()
  }

  /* TODO: Handle multi-line output, e.g. multiple error messages. */

  protected def readSuccess() {
    val answer = readLine()

    if (answer != "success")
      throw new ProverInteractionFailed(s"Unexpected output of $proverName. Expected 'success' but found: $answer")
  }

  protected def readUnsat(): Boolean = readLine() match {
    case "unsat" => true
    case "sat" => false
    case "unknown" => false

    case result =>
      throw new ProverInteractionFailed(s"Unexpected output of $proverName while trying to refute an assertion: $result")
  }

  protected def readLine(): String = {
    var repeat = true
    var result = ""

    while (repeat) {
      result = input.readLine()
      if (result.toLowerCase != "success") logComment(result)

      val warning = result.startsWith("WARNING")
      if (warning) log.info(s"$proverName: $result")

      repeat = warning
    }

    result
  }

  protected def logToFile(str: String) {
    logFile.println(str)
  }

  protected def writeLine(out: String) = {
    logToFile(out)
    output.println(out)
  }

  def setTimeout(timeout: Int)
}
