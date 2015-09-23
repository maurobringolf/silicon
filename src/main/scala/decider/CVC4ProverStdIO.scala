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


class CVC4ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends ProverStdIO(config, bookkeeper) {

  // Assuming this does not change during runtime.
  proverPath = Paths.get(config.z3Exe) // TODO: FIX!

  protected def createInstance() = {
    log.info(s"Starting Z3 at ${proverPath}")

    val userProvidedZ3Args: Array[String] = config.z3Args.get match {
      case None =>
        Array()

      case Some(args) =>
        log.info(s"Additional command-line arguments are $args")
        args.split(' ').map(_.trim)
    }

    val builder = new ProcessBuilder(proverPath.toFile.getPath +: "--lang smt" +: userProvidedZ3Args :_*)
    builder.redirectErrorStream(true)

    val process = builder.start()

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        process.destroy()
      }
    })

    process
  }

  def setTimeout(timeout: Int) {}
}
