package viper.silicon.verifier

import viper.silver.ast

// TODO: Would probably make more sense to have all of this in Silver
object LanguageFeature extends Enumeration {
  type LanguageFeature = Value
  val MagicWands, QuantifiedPermissions, QuantifiedFields, QuantifiedPredicates, QuantifiedMagicWands = Value

  def isUsedBy(program: ast.Program, lf: LanguageFeature) : Boolean = lf match {
    case MagicWands => !program.magicWandStructures.isEmpty
    case QuantifiedFields => !ast.utility.QuantifiedPermissions.quantifiedFields(program, program).isEmpty
    case QuantifiedPredicates => !ast.utility.QuantifiedPermissions.quantifiedPredicates(program, program).isEmpty
    case QuantifiedMagicWands => !ast.utility.QuantifiedPermissions.quantifiedMagicWands(program, program).isEmpty
    case QuantifiedPermissions => (!isUsedBy(program, QuantifiedFields)
                                  || !isUsedBy(program, QuantifiedPredicates)
                                  || !isUsedBy(program, QuantifiedMagicWands))
  }
}
