package viper.silicon.tests

import org.scalatest.DoNotDiscover

@DoNotDiscover
class FrontendGeneratedTests extends PortableSiliconTests {
  override val testDirectories = Seq("src/test/resources/frontend-generated")
}
