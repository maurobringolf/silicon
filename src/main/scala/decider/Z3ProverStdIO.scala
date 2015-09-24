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


class Z3ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends ProverStdIO(config, bookkeeper) {

  // Assuming this does not change during runtime.
  val path = Paths.get(config.z3Exe)

  def name = Z3ProverStdIO.name
  def exeEnvVar = Z3ProverStdIO.exeEnvVar
  def startupArgs = Z3ProverStdIO.startupArgs
  def minVersion = Z3ProverStdIO.minVersion
  def maxVersion = Z3ProverStdIO.maxVersion

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

object Z3ProverStdIO {
  val name = "Z3"
  val exeEnvVar = "Z3_EXE"
  val startupArgs = List("-smt2", "-in")

  val minVersion = Version("4.3.2")
  val maxVersion = None
}