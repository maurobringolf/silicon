package viper.silicon.tests

import viper.silicon.interfaces.UnsupportedInputReason
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput, TestError, TestAdditionalOutputError, SilOutput}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult, errors}

class FrontendGeneratedTests extends PortableSiliconTests {
  override val testDirectories = Seq("src/test/resources/frontend-generated")

  override def errorShouldLeadToTestCancel(err: TestError) = err match {
    case TestAdditionalOutputError(SilOutput(errors.Internal(_,UnsupportedInputReason,_))) => true
    case _ => super.errorShouldLeadToTestCancel(err)
  }
}
