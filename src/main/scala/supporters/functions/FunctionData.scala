// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.FatalResult
import viper.silicon.rules.{InverseFunctions, SnapshotMapDefinition, functionSupporter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef._
import viper.silicon.state.{Identifier, IdentifierFactory, SymbolConverter}
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

  lazy val qpInversesMap : QPinvMap = if (programFunction.pres.isEmpty) Map.empty else getQPInversesMap(programFunction.pres.reduce((p1,p2) => ast.And(p1,p2)()))

  def qpInverses : Seq[Fun] = qpInversesMap.map(_._2._1).toSeq
  def qpInversesAxioms : Seq[Term] = qpInversesMap.flatMap(_._2._2).toSeq

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

  // Maps a QP assertion (identified by program position) to its inverse receiver function and axioms for it
  type QPinvMap = Map[ast.Position, (Fun, Seq[Term])]
  // TODO: Use Resource ast type instead of general K type parameter
  // Maps a resource to a Boolean term parametrized by the receiver
  // e.g. If field f maps to function g, then g(x):Bool is a Term describing the condition under
  // which x:Ref is in the f-domain.
  type DomMap[K] = Map[K, Term => Term]

  def translatePreconditionToDomain(pre: ast.Exp): Option[Term] = pre match {
    case ast.PredicateAccessPredicate(ast.PredicateAccess(args, p), _) =>
      val tArgs = expressionTranslator.translatePrecondition(program, args, this)
      Some(PHeapSingletonPredicate(p, tArgs, PHeapLookupPredicate(p, `?h`, tArgs)))
    case ast.And(e1, e2) =>
    translatePreconditionToDomain(e1).flatMap(d1 => {
      translatePreconditionToDomain(e2).map(d2 => PHeapCombine(d1, d2))
      })
    case ast.FieldAccessPredicate(ast.FieldAccess(x, f), _) =>
      val tx = expressionTranslator.translatePrecondition(program, Seq(x), this)(0)
      Some(PHeapSingletonField(f.name,tx, PHeapLookupField(f.name, symbolConverter.toSort(f.typ), `?h`, tx)))
    case ast.CondExp(iff, thn, els) =>
      val tIff = expressionTranslator.translatePrecondition(program, Seq(iff), this)(0)
      translatePreconditionToDomain(thn).flatMap(dthn => {
        translatePreconditionToDomain(els).map(dels => Ite(tIff, dthn, dels))
      })
    case ast.Implies(prem, conc) =>
      translatePreconditionToDomain(conc).map(dConc => {
        val tPerm = expressionTranslator.translatePrecondition(program, Seq(prem), this)(0)
        Ite(tPerm, dConc, predef.Emp)
      })
    case e: ast.InhaleExhaleExp =>
      translatePreconditionToDomain(e.whenExhaling)
    case ast.Let(v,e,body) =>
      translatePreconditionToDomain(body.replace(v.localVar, e))
    case a =>
      if (a.isPure) Some(predef.Emp) else None //sys.error("Cannot translatePreconditionToDomain() of " + a.toString + " of type " + a.getClass)
  }
  
  def restrictHeapAxiom() : Term = {

    val translatedDomains = programFunction.pres.map(pre => {
        translatePreconditionToDomain(pre)    
    })

    val preContainsQP = translatedDomains.exists(d => d.isEmpty)

    if (!preContainsQP) {
      val dom = if (programFunction.pres.isEmpty) predef.Emp else translatedDomains.map(_.get).reduce((h1, h2) => PHeapCombine(h1,h2))
      return Forall(arguments, restrictHeapApplication === dom, Trigger(restrictHeapApplication), s"restrictHeapAxiom [${function.id.name}]")
    } else {
      val pre = if (programFunction.pres.isEmpty) ast.BoolLit(true)() else programFunction.pres.reduce((p1,p2) => ast.And(p1,p2)())
      val fieldDoms : DomMap[ast.Field] = getFieldDoms(pre)

      val predDoms : DomMap[ast.Predicate] = getPredDoms(pre)

      val d1 = predDoms.iterator.map({ case (p, dom) => {
        val pArgs = p.formalArgs.map(x => Var(identifierFactory.fresh(x.name), symbolConverter.toSort(x.typ)))
        val x = Var(identifierFactory.fresh("loc"), sorts.Loc)

        Forall( arguments
              , Forall( pArgs
                      , Let(x, PHeapPredicateLoc(p.name, pArgs),
                          And( Iff(SetIn(x, PHeapPredicateDomain(p.name, restrictHeapApplication)), dom(   PHeapPredicateLoc(p.name, pArgs)  ))
                            , Implies(SetIn(x, PHeapPredicateDomain(p.name, restrictHeapApplication)), PHeapLookupPredicate(p.name, restrictHeapApplication, pArgs) === PHeapLookupPredicate(p.name, `?h`, pArgs))))
                      , Seq( Trigger(SetIn(PHeapPredicateLoc(p.name, pArgs), PHeapPredicateDomain(p.name, restrictHeapApplication)))
                          , Trigger(PHeapLookupPredicate(p.name, restrictHeapApplication, pArgs)))
                      )
              , Seq(Trigger(restrictHeapApplication))
              , s"restrictHeapAxiom_dom_${p.name}[${function.id.name}]")
      }}).foldLeft[Term](True())((d1,d2) => And(d1,d2))

      val d2 = fieldDoms.iterator.map({ case (ast.Field(name, typ), dom) => {
        val x = Var(identifierFactory.fresh("x"), sorts.Ref)
        val fSort = symbolConverter.toSort(typ)

        Forall( arguments
              , Forall( Seq(x)
                      , And( Iff(SetIn(x, PHeapFieldDomain(name, restrictHeapApplication)), dom(x))
                          , PHeapLookupField(name, fSort, restrictHeapApplication, x) === PHeapLookupField(name, fSort, `?h`, x))
                      , Seq( Trigger(PHeapLookupField(name, fSort, restrictHeapApplication, x))
                          , Trigger(SetIn(x, PHeapFieldDomain(name, restrictHeapApplication)))))
              , Seq(Trigger(restrictHeapApplication))
              , s"restrictHeapAxiom_dom_${name}[${function.id.name}]")
      }}).foldLeft[Term](True())((d1,d2) => And(d1,d2))

      return And(d1, d2)
    }
  }

  def getQPInversesMap(pre: ast.Exp): QPinvMap = pre match {
    case ast.And(e1,e2) => getQPInversesMap(e1) ++ getQPInversesMap(e2)
    case node@QuantifiedPermissionAssertion(forall,cond,ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), perm: ast.Exp)) => {
      val qSort = symbolConverter.toSort(forall.variables.head.typ)

      val proxyFa = ast.Forall(forall.variables, Seq(), ast.BoolLit(true)())()

      val Seq(tFa, tRcv, tCond, tPerm) = expressionTranslator.translatePrecondition(program, Seq(proxyFa, rcv, cond, perm), this)
      val qi = tFa.asInstanceOf[Quantification].vars.head

      // TODO: Use better naming, probably just line number
      val inv = Fun( Identifier("inv_" ++ node.getPrettyMetadata._1.toString)
                   , sorts.Ref +: arguments.tail.map(_.sort)
                   , qSort)

      val leftInverse = Forall( qi +: arguments.tail
                              , Implies(And(tCond, Greater(tPerm, Zero)), (App(inv, tRcv +: arguments.tail) === qi))
                              , Seq(Trigger(App(inv, tRcv +: arguments.tail)))
                              , "leftInverse")
      
      val r = Var(identifierFactory.fresh("r"), sorts.Ref)
      val tCondr = tCond.replace(qi, App(inv,r +: arguments.tail))
      val tPermr = tPerm.replace(qi, App(inv,r +: arguments.tail))
      val tRcvr = tRcv.replace(qi, App(inv,r +: arguments.tail))
      val rightInverse = Forall( r +: arguments.tail
                              , Implies(And(tCondr, Greater(tPermr, Zero)), tRcvr === r)
                              , Seq(Trigger(App(inv,r +: arguments.tail)))
                              , "rightInverse")

      Map(node.getPrettyMetadata._1 -> (inv, Seq(leftInverse, rightInverse)))
    }
    case _ => Map.empty
  }

  def mergeDoms[K](fd1: DomMap[K] , fd2: DomMap[K]) : DomMap[K] = {
    val fs = fd1.keySet ++ fd2.keySet
    toMap(fs.map(k => (k, ((x:Term) => Or(
      fd1.getOrElse(k, (_:Term) => False())(x),
      fd2.getOrElse(k, (_:Term) => False())(x),
    )))))
  }

  def getFieldDoms(pre: ast.Exp) : DomMap[ast.Field] = pre match {
    case ast.And(e1,e2) => mergeDoms(getFieldDoms(e1), getFieldDoms(e2))
    case ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), _) => {
      val tRcv = expressionTranslator.translatePrecondition(program, Seq(rcv), this).head
      Map(f -> (x => x === tRcv))
    }
    case n@QuantifiedPermissionAssertion(forall, cond, ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), p: ast.Exp)) => {
      val (inv, invAx) = qpInversesMap(n.getPrettyMetadata._1)
      val proxyFa = ast.Forall(forall.variables, Seq(), ast.And(cond, ast.GtCmp(p, ast.IntLit(0)())())())()
      val Seq(tFa) = expressionTranslator.translatePrecondition(program, Seq(proxyFa), this)
      
      val i = tFa.asInstanceOf[Quantification].vars.head
      Map(f -> (r => tFa.asInstanceOf[Quantification].body.replace(i, App(inv, r +: arguments.tail))))
    }
    case a => toMap(program.fields.zip(Seq.fill(program.fields.length){(_:Term) => False()}))
  }

  def getPredDoms(pre: ast.Exp): DomMap[ast.Predicate] = pre match {
    case ast.And(e1, e2) => mergeDoms(getPredDoms(e1), getPredDoms(e2))
    case ast.PredicateAccessPredicate(ast.PredicateAccess(args, p), _) => {
      val tArgs = expressionTranslator.translatePrecondition(program, args, this)

      Map(program.findPredicate(p) -> (x => {
        // TODO: Stop hacking
        val pArgs = x.asInstanceOf[PHeapPredicateLoc].args
        And( pArgs.zip(tArgs).map({ case (a,b) => a === b }))
        //x === PHeapPredicateLoc(p, tArgs)
      }))
    }
    case a => Map.empty
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
