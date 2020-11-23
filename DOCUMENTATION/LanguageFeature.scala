package viper.silver.ast.utility

import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Rewritable

object LanguageFeature extends Enumeration {
  type LanguageFeature = Value
  val MagicWands, QuantifiedPermissions, QuantifiedFields, QuantifiedPredicates, QuantifiedMagicWands, MagicWandFunction = Value

  implicit class LanguageFeatureValue(lf: Value) {
    /**
      * Returns all the AST nodes that use the feature `lf`
      */
    def isUsedBy(program: ast.Program) : List[ast.Node with Positioned with TransformableErrors with Rewritable] = {
      lf match {
        case MagicWands => program.magicWandStructures.toList
        case QuantifiedFields => ast.utility.QuantifiedPermissions.quantifiedFields(program, program).toList
        case QuantifiedPredicates => ast.utility.QuantifiedPermissions.allQuantifiedPredicates(program).toList
        case QuantifiedMagicWands => ast.utility.QuantifiedPermissions.quantifiedMagicWands(program, program).toList
        case QuantifiedPermissions => QuantifiedMagicWands.isUsedBy(program) ++ QuantifiedFields.isUsedBy(program) ++ QuantifiedPredicates.isUsedBy(program)
        case MagicWandFunction => program.functions.filter(f => !f.pres.flatMap(pre => pre.deepCollect({ case _: ast.MagicWand => true})).isEmpty).toList
      }
    }
  }
}
