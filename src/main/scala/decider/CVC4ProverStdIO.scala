/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import java.nio.file.Paths
import viper.silicon.common.config.Version
import viper.silicon.reporting.Bookkeeper


class CVC4ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends ProverStdIO(config, bookkeeper) {

  // Assuming this does not change during runtime.
  val path = Paths.get(config.cvc4Exe)

  def name = CVC4ProverStdIO.name
  def exeEnvVar = CVC4ProverStdIO.exeEnvVar
  def startupArgs = CVC4ProverStdIO.startupArgs
  def minVersion = CVC4ProverStdIO.minVersion
  def maxVersion = CVC4ProverStdIO.maxVersion
  def staticConfigResource = CVC4ProverStdIO.staticConfigResource

  def setTimeout(timeout: Int): Unit = {
    logComment(s"Setting the timeout ($timeout ms) interactively is not supported by CVC4")
  }
}

object CVC4ProverStdIO {
  val name = "CVC4"
  val exeEnvVar = "CVC4_EXE"
  val startupArgs = List("--lang smt")

  val minVersion = Version("1.5")
  val maxVersion = None
  val staticConfigResource = "/cvc4config.smt2"
}