/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.{JSTreeRenderer, SymbExLogger}
import viper.silicon.interfaces.Failure
import viper.silicon.verifier.Verifier
import viper.silver.ast.Member
import viper.silver.verifier.{AbstractVerificationError, VerificationError}
import viper.silver.verifier.errors.VerificationErrorWithCounterexample

trait SymbolicExecutionRules extends Immutable {
  protected def failure(ve: VerificationError, v: Verifier, generateNewModel: Boolean = false): Failure = {
    if (v != null && Verifier.config.ideModeAdvanced()) {
      if (generateNewModel) {
        v.decider.generateModel()
      }
      val model = v.decider.getModel()
      val jsRenderer = new JSTreeRenderer()
      val symState = jsRenderer.render(SymbExLogger.memberList)
      SymbExLogger.printError(ve.toString, model)
      val currentMember = if (SymbExLogger.memberList.length > 0 && SymbExLogger.memberList.last.main.isInstanceOf[Member]) SymbExLogger.memberList.last.main.value.asInstanceOf[Member].name else "UNKNOWN"
      Failure(VerificationErrorWithCounterexample(ve.asInstanceOf[AbstractVerificationError], model, symState, currentMember))
    }else {
      Failure(ve)
    }
  }
}
