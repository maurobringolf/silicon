/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.SymbExLogger
import viper.silicon.interfaces.Failure
import viper.silicon.verifier.Verifier
import viper.silver.verifier.VerificationError

trait SymbolicExecutionRules extends Immutable {
  protected def failure(ve: VerificationError, v: Verifier, generateNewModel: Boolean = false): Failure = {
    if (v != null && Verifier.config.ideModeAdvanced()) {
      if (generateNewModel) {
        v.decider.generateModel()
      }
      val model = v.decider.getModel()
      SymbExLogger.printError(ve.toString, model)
    }
    Failure(ve)
  }
}
