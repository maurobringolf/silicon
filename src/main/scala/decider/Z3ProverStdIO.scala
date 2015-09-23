/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */
package viper
package silicon
package decider

import java.nio.file.Paths

import viper.silicon.reporting.Bookkeeper


/* TODO: Pass a logger, don't open an own file to log to. */
class Z3ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends ProverStdIO(config, bookkeeper) {

  // Assuming this does not change during runtime.
  proverPath = Paths.get(config.z3Exe)

  protected def createInstance() = {
    log.info(s"Starting Z3 at ${proverPath}")

    val userProvidedZ3Args: Array[String] = config.z3Args.get match {
      case None =>
        Array()

      case Some(args) =>
        log.info(s"Additional command-line arguments are $args")
        args.split(' ').map(_.trim)
    }

    val builder = new ProcessBuilder(proverPath.toFile.getPath +: "-smt2" +: "-in" +: userProvidedZ3Args :_*)
    builder.redirectErrorStream(true)

    val process = builder.start()

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        process.destroy()
      }
    })
    process
  }

  def setTimeout(timeout: Int) {
    /* [2015-07-27 Malte] Setting the timeout unnecessarily often seems to
     * worsen performance, if only a bit. For the current test suite of
     * 199 Silver files, the total verification time increased from 60s
     * to 70s if 'set-option' is emitted every time.
     */
    if (lastTimeout != timeout) {
      lastTimeout = timeout

      writeLine(s"(set-option :timeout $timeout)")
      readSuccess()
    }
  }
}
