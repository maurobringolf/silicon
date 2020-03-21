// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.FatalResult
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition, functionSupporter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef._
import viper.silicon.state.{IdentifierFactory, SymbolConverter}
import viper.silicon.supporters.PredicateData
import viper.silicon.{Config, Map, toMap}

/* TODO: Refactor FunctionData!
 *       Separate computations from "storing" the final results and sharing
 *       them with other components. Computations should probably be moved to the
 *       FunctionVerificationUnit.
 */
class FunctionData(val programFunction: ast.Function,
                   val height: Int,
                   val quantifiedFields: InsertionOrderedSet[ast.Field],
                   val program: ast.Program)
                  /* Note: Holding references to fixed symbol converter, identifier factory, ...
                   *       (instead of going through a verifier) is only safe if these are
                   *       either effectively independent of verifiers or if they are not used
                   *       with/in the context of different verifiers.
                   */
                  (symbolConverter: SymbolConverter,
                   expressionTranslator: HeapAccessReplacingExpressionTranslator,
                   identifierFactory: IdentifierFactory,
                   predicateData: ast.Predicate => PredicateData,
                   config: Config) {

  private[this] var phase = 0

  /*
   * Properties computed from the constructor arguments
   */

  val function: HeapDepFun = symbolConverter.toFunction(programFunction)
  val limitedFunction = functionSupporter.limitedVersion(function)
  val statelessFunction = functionSupporter.statelessVersion(function)
  val restrictHeapFunction = functionSupporter.restrictHeapFunction(function)

  val formalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(identifierFactory.fresh(x.name),
               symbolConverter.toSort(x.typ)))

  val formalResult = Var(identifierFactory.fresh(programFunction.result.name),
                         symbolConverter.toSort(programFunction.result.typ))

  val arguments = Seq(`?h`) ++ formalArgs.values

  val functionApplication = App(function, `?h` +: formalArgs.values.toSeq)
  val restrictHeapApplication = App(restrictHeapFunction, arguments)
  val restrictedLimitedFunctionApplication = App(limitedFunction, restrictHeapApplication +: formalArgs.values.toSeq)
  val limitedFunctionApplication = App(limitedFunction, `?h` +: formalArgs.values.toSeq)
  val triggerFunctionApplication = App(statelessFunction, formalArgs.values.toSeq)

  val limitedAxiom =
    Forall(arguments,
           restrictedLimitedFunctionApplication === functionApplication,
           Trigger(functionApplication),
           s"limitedAxiom [${function.id.name}]")

  val triggerAxiom =
    Forall(arguments, triggerFunctionApplication, Trigger(limitedFunctionApplication), s"triggerAxiom [${function.id.name}]")
  
  def restrictHeapAxiom() : Term = {
    val dom = if (programFunction.pres.isEmpty) predef.Emp else programFunction.pres.map(pre => {
      translatePreconditionToDomain(pre)
    }).reduce((h1, h2) => PHeapCombine(h1,h2))

    Forall(arguments, restrictHeapApplication === dom, Trigger(restrictHeapApplication), s"restrictHeapAxiom [${function.id.name}]")
  }

  def translatePreconditionToDomain(pre: ast.Exp): Term = pre match {
    case ast.PredicateAccessPredicate(ast.PredicateAccess(args, p), _) =>
      val tArgs = expressionTranslator.translatePrecondition(program, args, this)
      PHeapSingletonPredicate(p, tArgs, PHeapLookupPredicate(p, `?h`, tArgs))
    case ast.And(e1, e2) =>
      PHeapCombine(translatePreconditionToDomain(e1), translatePreconditionToDomain(e2))
    case ast.FieldAccessPredicate(ast.FieldAccess(x, f), _) =>
      val tx = expressionTranslator.translatePrecondition(program, Seq(x), this)(0)
      PHeapSingletonField(f.name,tx, PHeapLookupField(f.name, symbolConverter.toSort(f.typ), `?h`, tx))
    case ast.CondExp(iff, thn, els) =>
      Ite(expressionTranslator.translatePrecondition(program, Seq(iff), this)(0), translatePreconditionToDomain(thn), translatePreconditionToDomain(els))
    case ast.Implies(prem, conc) =>
      Ite(expressionTranslator.translatePrecondition(program, Seq(prem), this)(0), translatePreconditionToDomain(conc), predef.Emp)
    case e: ast.InhaleExhaleExp =>
      translatePreconditionToDomain(e.whenExhaling)
    case ast.Let(v,e,body) =>
      translatePreconditionToDomain(body.replace(v.localVar, e))
    case a =>
      if (a.isPure) predef.Emp else sys.error("Cannot translatePreconditionToDomain() of " + a.toString + " of type " + a.getClass)
  }

  /*
   * Data collected during phases 1 (well-definedness checking) and 2 (verification)
   */

  /* TODO: Analogous to fresh FVFs, Nadja records PSFs in the FunctionRecorder,
   *       but they are never used. My guess is, that QP assertions over predicates
   *       are currently not really supported (incomplete? unsound?)
   */

  private[functions] var verificationFailures: Seq[FatalResult] = Vector.empty
  private[functions] var locToSnap: Map[ast.LocationAccess, Term] = Map.empty
  private[functions] var fappToSnap: Map[ast.FuncApp, Term] = Map.empty
  private[this] var freshFvfsAndDomains: InsertionOrderedSet[SnapshotMapDefinition] = InsertionOrderedSet.empty
  private[this] var freshFieldInvs: InsertionOrderedSet[InverseFunctions] = InsertionOrderedSet.empty
  private[this] var freshArps: InsertionOrderedSet[(Var, Term)] = InsertionOrderedSet.empty
  private[this] var freshSnapshots: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshPathSymbols: InsertionOrderedSet[Function] = InsertionOrderedSet.empty
  private[this] var freshMacros: InsertionOrderedSet[MacroDecl] = InsertionOrderedSet.empty
  private[this] var freshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  private[functions] def getFreshFieldInvs: InsertionOrderedSet[InverseFunctions] = freshFieldInvs
  private[functions] def getFreshArps: InsertionOrderedSet[Var] = freshArps.map(_._1)
  private[functions] def getFreshSymbolsAcrossAllPhases: InsertionOrderedSet[Decl] = freshSymbolsAcrossAllPhases

  private[functions] def advancePhase(recorders: Seq[FunctionRecorder]): Unit = {
    assert(0 <= phase && phase <= 1, s"Cannot advance from phase $phase")

    val mergedFunctionRecorder: FunctionRecorder =
      if (recorders.isEmpty)
        NoopFunctionRecorder
      else
        recorders.tail.foldLeft(recorders.head)((summaryRec, nextRec) => summaryRec.merge(nextRec))

    locToSnap = mergedFunctionRecorder.locToSnap
    fappToSnap = mergedFunctionRecorder.fappToSnap
    freshFvfsAndDomains = mergedFunctionRecorder.freshFvfsAndDomains
    freshFieldInvs = mergedFunctionRecorder.freshFieldInvs
    freshArps = mergedFunctionRecorder.freshArps
    freshSnapshots = mergedFunctionRecorder.freshSnapshots
    freshPathSymbols = mergedFunctionRecorder.freshPathSymbols
    freshMacros = mergedFunctionRecorder.freshMacros

    freshSymbolsAcrossAllPhases ++= freshPathSymbols map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshArps.map(pair => FunctionDecl(pair._1))
    freshSymbolsAcrossAllPhases ++= freshSnapshots map FunctionDecl
    freshSymbolsAcrossAllPhases ++= freshFieldInvs.flatMap(_.inverses map FunctionDecl)
    freshSymbolsAcrossAllPhases ++= freshMacros

    freshSymbolsAcrossAllPhases ++= freshFvfsAndDomains map (fvfDef =>
      fvfDef.sm match {
        case x: Var => ConstDecl(x)
        case App(f: Function, _) => FunctionDecl(f)
        case other => sys.error(s"Unexpected SM $other of type ${other.getClass.getSimpleName}")
      })

    phase += 1
  }

  private def generateNestedDefinitionalAxioms: InsertionOrderedSet[Term] = (
    //   freshFieldInvs.flatMap(_.definitionalAxioms)
    //++ freshFvfsAndDomains.flatMap (fvfDef => fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
    freshArps.map(_._2)
  )

  /*
   * Properties resulting from phase 1 (well-definedness checking)
   */

  lazy val translatedPres: Seq[Term] = {
    assert(1 <= phase && phase <= 2, s"Cannot translate precondition in phase $phase")

    expressionTranslator.translatePrecondition(program, programFunction.pres, this)
  }

  lazy val postAxiom: Option[Term] = {
    assert(phase == 1, s"Postcondition axiom must be generated in phase 1, current phase is $phase")

    if (programFunction.posts.nonEmpty) {
      val posts =
        expressionTranslator.translatePostcondition(program, programFunction.posts, this)

      val pre = And(translatedPres)
      val innermostBody = And(generateNestedDefinitionalAxioms ++ List(Implies(pre, And(posts))))
      val bodyBindings: Map[Var, Term] = Map(formalResult -> limitedFunctionApplication)
      val body = Let(toMap(bodyBindings), innermostBody)

      Some(Forall(arguments, body, Trigger(limitedFunctionApplication), s"postAxiom [${function.id.name}]"))
    } else
      None
  }

  /*
   * Properties resulting from phase 2 (verification)
   */

  lazy val predicateTriggers: Map[ast.Predicate, App] = {
    val recursiveCallsAndUnfoldings: Seq[(ast.FuncApp, Seq[ast.Unfolding])] =
      Functions.recursiveCallsAndSurroundingUnfoldings(programFunction)

    val outerUnfoldings: Seq[ast.Unfolding] =
      recursiveCallsAndUnfoldings.flatMap(_._2.headOption)

    val predicateAccesses: Seq[ast.PredicateAccess] =
      if (recursiveCallsAndUnfoldings.isEmpty)
        Vector.empty
      //        programFunction.pres flatMap (pre =>
      //          pre.shallowCollect { case predacc: ast.PredicateAccess => predacc })
      else
        outerUnfoldings map (_.acc.loc)

    toMap(predicateAccesses.map(predacc => {
      val predicate = program.findPredicate(predacc.predicateName)
      val triggerFunction = predicateData(predicate).triggerFunction

      /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
      val tArgs = expressionTranslator.translatePrecondition(program, predacc.args, this)
      val args = (
        PHeapLookupPredicate(predacc.predicateName, predef.`?h`, tArgs)
      +: tArgs)

      val fapp = App(triggerFunction, args)

      predicate -> fapp
    }))
  }

  lazy val definitionalAxiom: Option[Term] = {
    assert(phase == 2, s"Definitional axiom must be generated in phase 2, current phase is $phase")

    val optBody = expressionTranslator.translate(program, programFunction, this)

    optBody.map(translatedBody => {
      val pre = And(translatedPres)
      val nestedDefinitionalAxioms = generateNestedDefinitionalAxioms
      val innermostBody = And(nestedDefinitionalAxioms ++ List(Implies(pre, And(functionApplication === translatedBody))))
      val bodyBindings: Map[Var, Term] = Map(formalResult -> limitedFunctionApplication)
      val body = Let(toMap(bodyBindings), innermostBody)
      val allTriggers = (
           Seq(Trigger(functionApplication))
        ++ predicateTriggers.values.map(pt => Trigger(Seq(triggerFunctionApplication, pt))))

      Forall(arguments, body, allTriggers)})
  }
}
