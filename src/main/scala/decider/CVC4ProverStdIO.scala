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

  proverName = "CVC4"
  startupArgs = List("--lang smt")

  // Assuming this does not change during runtime.
  proverPath = Paths.get(config.cvc4Exe)


  def setTimeout(timeout: Int): Unit = {
    logComment(s"Setting the timeout ($timeout ms) interactively is not supported by CVC4")
  }
}
