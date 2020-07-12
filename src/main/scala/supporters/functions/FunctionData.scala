// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters.functions

import com.typesafe.scalalogging.LazyLogging
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
import viper.silver.plugin.PluginAwareReporter

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
                   config: Config,
                   reporter: PluginAwareReporter)
    extends LazyLogging {

  private[this] var phase = 0

  /*
   * Properties computed from the constructor arguments
   */

  val function: HeapDepFun = symbolConverter.toFunction(programFunction)
  val limitedFunction = functionSupporter.limitedVersion(function)
  val statelessFunction = functionSupporter.statelessVersion(function)
  val restrictHeapFunction = functionSupporter.restrictHeapFunction(function)

  // Maps a QP assertion (identified by program position) to its inverse receiver functions with axioms (one per quantified variable)
  type QPinvMap = Map[ast.Position, (Seq[Term], Map[Var, Fun])]

  lazy val qpInversesMap : QPinvMap = if (programFunction.pres.isEmpty) Map.empty else getQPInversesMap(programFunction.pres.reduce((p1,p2) => ast.And(p1,p2)()))

  def qpInverses : Iterable[Fun] = qpInversesMap.values.flatMap(_._2.values)
  def qpInversesAxioms : Iterable[Term] = qpInversesMap.values.flatMap(_._1)

  val formalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(identifierFactory.fresh(x.name),
               symbolConverter.toSort(x.typ)))

  val axiomFormalArgs: Map[ast.AbstractLocalVar, Var] = toMap(
    for (arg <- programFunction.formalArgs;
         x = arg.localVar)
    yield
      x -> Var(Identifier(x.name),
               symbolConverter.toSort(x.typ)))

  val formalResult = Var(identifierFactory.fresh(programFunction.result.name),
                         symbolConverter.toSort(programFunction.result.typ))

  val arguments = Seq(`?h`) ++ formalArgs.values
  val axiomArguments = functionSupporter.axiomSnapshotVariable +: axiomFormalArgs.values.toSeq

  val functionApplication = App(function, axiomArguments)
  val restrictHeapApplication = App(restrictHeapFunction, axiomArguments)
  val limitedFunctionApplication = App(limitedFunction, axiomArguments)
  val triggerFunctionApplication = App(statelessFunction, axiomFormalArgs.values.toSeq)

  val h1 = Var(Identifier("@h1"), sorts.PHeap)
  val h2 = Var(Identifier("@h2"), sorts.PHeap)

  val framingAxiom =
    Forall( Seq(h1, h2) ++ axiomArguments.tail
          , Implies(PHeapEqual(App(restrictHeapFunction, h1 +: axiomArguments.tail), App(restrictHeapFunction, h2 +: axiomArguments.tail)), App(limitedFunction, h1 +: axiomArguments.tail) === App(limitedFunction, h2 +: axiomArguments.tail))
          , Seq(Trigger(Seq(App(limitedFunction, h1 +: axiomArguments.tail), App(limitedFunction, h2 +: axiomArguments.tail))))
          , s"framingAxiom [${function.id.name}]"
          )

  val limitedAxiom =
    Forall(axiomArguments,
           limitedFunctionApplication === functionApplication,
           Trigger(functionApplication),
           s"limitedAxiom [${function.id.name}]")

  val triggerAxiom =
    Forall(axiomArguments, triggerFunctionApplication, Trigger(limitedFunctionApplication), s"triggerAxiom [${function.id.name}]")

  // TODO: Use Resource ast type instead of general K type parameter
  // Maps a resource to a Boolean term parametrized by the receiver
  // e.g. If field f maps to function g, then g(x):Bool is a Term describing the condition under
  // which (x:Ref) is in the f-domain of the function.
  type DomMap = Map[ast.Resource, Term => Term]

  def translatePreconditionToDomain(pre: ast.Exp): Option[Term] = pre match {
    case ast.PredicateAccessPredicate(ast.PredicateAccess(args, pred), p) =>
      val tArgs = expressionTranslator.translatePrecondition(program, args, this)
      val tCond = p match {
        case _: ast.WildcardPerm => True()
        case _ =>
          val tp = expressionTranslator.translatePrecondition(program, Seq(p), this).head
          Greater(tp, NoPerm())
      }
      Some(Ite( tCond
              , PHeapSingletonPredicate(pred, tArgs, PHeapLookupPredicate(pred, functionSupporter.axiomSnapshotVariable , tArgs))
              , predef.Emp
      ))
    case ast.And(e1, e2) =>
    translatePreconditionToDomain(e1).flatMap(d1 => {
      translatePreconditionToDomain(e2).map(d2 => PHeapCombine(d1, d2))
      })
    case ast.FieldAccessPredicate(ast.FieldAccess(x, f), p) =>
      val tx = expressionTranslator.translatePrecondition(program, Seq(x), this).head

      val tCond = p match {
        case _: ast.WildcardPerm => True()
        case _ =>
          val tp = expressionTranslator.translatePrecondition(program, Seq(p), this).head
          Greater(tp, NoPerm())
      }
      /**
       * [2020-07-11 Mauro]
       *
       * Note that unfoldings are irrelevant in this case and we can always use PHeapLookupField of the snapshot passed to the function,
       * because impure expressions under unfoldings are disallowed.
       *
       **/
      Some(Ite( tCond
              , PHeapSingletonField(f.name,tx, PHeapLookupField(f.name, symbolConverter.toSort(f.typ), functionSupporter.axiomSnapshotVariable , tx))
              , predef.Emp
      ))
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
      return Forall(axiomArguments, restrictHeapApplication === dom, Trigger(restrictHeapApplication), s"restrictHeapAxiom [${function.id.name}]")
    } else {
      val pre = if (programFunction.pres.isEmpty) ast.BoolLit(true)() else programFunction.pres.reduce((p1,p2) => ast.And(p1,p2)())

      val domMap = getDomMap(pre)

      domMap.iterator.map({
        case (p: ast.Predicate, dom: (Term => Term)) => {
          val pArgs = p.formalArgs.map(x => Var(identifierFactory.fresh(x.name), symbolConverter.toSort(x.typ)))
          val x = Var(identifierFactory.fresh("loc"), sorts.Loc)

          Forall( axiomArguments
                , Forall( Seq(x)
                        , And( Iff(SetIn(x, PHeapPredicateDomain(p.name, restrictHeapApplication)), dom(x))
                             , Implies(SetIn(x, PHeapPredicateDomain(p.name, restrictHeapApplication)), PHeapLookupPredicate(p.name, restrictHeapApplication, Seq(x)) === PHeapLookupPredicate(p.name, axiomArguments.head, Seq(x))))
                        , Seq( Trigger(SetIn(x, PHeapPredicateDomain(p.name, restrictHeapApplication)))
                            , Trigger(PHeapLookupPredicate(p.name, restrictHeapApplication, Seq(x)))))
                , Seq(Trigger(restrictHeapApplication))
                , s"restrictHeapAxiom_dom_${p.name}[${function.id.name}]")
        }
        case (ast.Field(name, typ), dom: (Term => Term)) => {
          val x = Var(identifierFactory.fresh("x"), sorts.Ref)
          val fSort = symbolConverter.toSort(typ)

          Forall( axiomArguments
                , Forall( Seq(x)
                        , And( Iff(SetIn(x, PHeapFieldDomain(name, restrictHeapApplication)), dom(x))
                            , PHeapLookupField(name, fSort, restrictHeapApplication, x) === PHeapLookupField(name, fSort, axiomArguments.head, x))
                        , Seq( Trigger(PHeapLookupField(name, fSort, restrictHeapApplication, x))
                            , Trigger(SetIn(x, PHeapFieldDomain(name, restrictHeapApplication)))))
                , Seq(Trigger(restrictHeapApplication))
                , s"restrictHeapAxiom_dom_${name}[${function.id.name}]")
        }
        case r => sys.error("Unexpected resource " ++ r.toString)
      }).foldLeft[Term](True())((d1,d2) => And(d1,d2))
    }
  }

  def getQPInversesMap(pre: ast.Exp): QPinvMap = pre match {
    case ast.And(e1,e2) => getQPInversesMap(e1) ++ getQPInversesMap(e2)
    case ast.CondExp(cond,e1,e2) => getQPInversesMap(e1) ++ getQPInversesMap(e2)
    case ast.Implies(prem, conc) => getQPInversesMap(conc)
    case node@QuantifiedPermissionAssertion(forall,cond,ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), perm: ast.Exp)) => {
      
      val proxyFa = ast.Forall(forall.variables, Seq(), ast.BoolLit(true)())()
      val notWildcardPerm: ast.Exp = perm match {
        case _:ast.WildcardPerm => ast.FullPerm()()
        case p => p
      }

      val Seq(tFa, tRcv, tCond, tPerm) = expressionTranslator.translatePrecondition(program, Seq(proxyFa, rcv, cond, notWildcardPerm), this)

      val qs = tFa.asInstanceOf[Quantification].vars

      val invs = qs.map(qi => {
        // TODO: Ideally we would use source position in the name,
        // such that the assocation is clear. But it seems that with macros
        // the positions are not maintained? For example the testcase 'quantifiedpermissions/misc/heap_dependent_triggers.vpr'
        // contains some edge cases.
        val invName = "QPinv_" ++ this.function.id.toString ++ "_" ++ node.getPrettyMetadata._1.toString ++ "_" ++ qi.id.name

        val inv = Fun( Identifier(invName)
                     , sorts.Ref +: axiomArguments.map(_.sort)
                     , qi.sort)

        val leftInverse = Forall( qs ++ axiomArguments
                                , Implies(And(tCond, Greater(tPerm, Zero)), (App(inv, tRcv +: axiomArguments) === qi))
                                , Seq(Trigger(App(inv, tRcv +: axiomArguments)))
                                , "leftInverse")
        (inv, leftInverse)
      })


      // There is only one right-inverse axiom
      val r = Var(identifierFactory.fresh("r"), sorts.Ref)
      val qsAsInvs = invs.map({ case (inv, _) => App(inv,r +: axiomArguments)})
      val tCondr = tCond.replace(qs, qsAsInvs)
      val tPermr = tPerm.replace(qs, qsAsInvs)
      val tRcvr = tRcv.replace(qs, qsAsInvs)
      val rightInverse = Forall( r +: axiomArguments
                              , Implies(And(tCondr, Greater(tPermr, Zero)), tRcvr === r)
                              , Seq(Trigger(qsAsInvs))
                              , "rightInverse")

      Map(node.getPrettyMetadata._1 -> ((rightInverse +: invs.map(_._2), toMap[Var, Fun](qs.zip(invs.map(_._1))))))
    }

    case node@QuantifiedPermissionAssertion(forall,cond,ast.PredicateAccessPredicate(ast.PredicateAccess(args, pred), perm: ast.Exp)) => {

      val proxyFa = ast.Forall(forall.variables, Seq(), ast.BoolLit(true)())()
      val notWildcardPerm: ast.Exp = perm match {
        case _:ast.WildcardPerm => ast.FullPerm()()
        case p => p
      }

      val Seq(tFa, tCond, tPerm) = expressionTranslator.translatePrecondition(program, Seq(proxyFa, cond, notWildcardPerm), this)
      val tArgs = expressionTranslator.translatePrecondition(program, args, this)

      val qs = tFa.asInstanceOf[Quantification].vars

      val invs = qs.map(qi => {
        // TODO: Ideally we would use source position in the name,
        // such that the assocation is clear. But it seems that with macros
        // the positions are not maintained? For example the testcase 'quantifiedpermissions/misc/heap_dependent_triggers.vpr'
        // contains some edge cases.
        val invName = "QPinv_" ++ this.function.id.toString ++ "_" ++ node.getPrettyMetadata._1.toString ++ "_" ++ qi.id.name

        val inv = Fun( Identifier(invName)
                     , sorts.Loc +: axiomArguments.map(_.sort)
                     , qi.sort)

        val leftInverse = Forall( qs ++ axiomArguments
                                , Implies(And(tCond, Greater(tPerm, Zero)), (App(inv, PHeapPredicateLoc(pred, tArgs) +: axiomArguments) === qi))
                                , Seq(Trigger(App(inv, PHeapPredicateLoc(pred, tArgs) +: axiomArguments)))
                                , "leftInverse")
        (inv, leftInverse)
      })

      // There is only one right-inverse axiom
      val r = Var(identifierFactory.fresh("l"), sorts.Loc)
      val qsAsInvs = invs.map({ case (inv,_) => App(inv,r +: axiomArguments) })
      val tCondr = tCond.replace(qs, qsAsInvs)
      val tPermr = tPerm.replace(qs, qsAsInvs)
      val tRcvr = PHeapPredicateLoc(pred, tArgs).replace(qs, qsAsInvs)

      val rightInverse = Forall( r +: axiomArguments
                              , Implies(And(tCondr, Greater(tPermr, Zero)), tRcvr === r)
                              , Seq(Trigger(qsAsInvs))
                              , "rightInverse")

      Map(node.getPrettyMetadata._1 -> ((rightInverse +: invs.map(_._2), toMap[Var, Fun](qs.zip(invs.map(_._1))))))
    }

    case _ => Map.empty
  }


  def getDomMap(pre: ast.Exp) : DomMap = {
    def mergeDoms(fd1: DomMap , fd2: DomMap, merger: (Term, Term) => Term = Or(_,_)) : DomMap = {
      val fs = fd1.keySet ++ fd2.keySet
      toMap(fs.map(k => (k, ((x:Term) => merger(
        fd1.getOrElse(k, (_:Term) => False())(x),
        fd2.getOrElse(k, (_:Term) => False())(x),
      )))))
    }

    // Takes an existing DomMap and extends it to include 'a'
    def go(a: ast.Exp, dm: DomMap) : DomMap = a match {
      
      // Single resource access
      case ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), p) => {
        val Seq(tRcv, tp) = expressionTranslator.translatePrecondition(program, Seq(rcv, p), this)
        Map(f -> (x => And(x === tRcv, Greater(tp, NoPerm()))))
      }
      case ast.PredicateAccessPredicate(ast.PredicateAccess(args, pred), p) => {
        val tArgs = expressionTranslator.translatePrecondition(program, args, this)
        val tp = expressionTranslator.translatePrecondition(program, Seq(p), this).head

        Map(program.findPredicate(pred) -> (x => {
          And(Greater(tp, NoPerm()), PHeapPredicateLoc(pred, tArgs) === x)
        }))
      }
      /** TODO
      case ast.MagicWand => {

      }
      */

      // Quantified resource access
      case n@QuantifiedPermissionAssertion(forall, cond, ast.FieldAccessPredicate(ast.FieldAccess(rcv: ast.Exp, f: ast.Field), p: ast.Exp)) => {
        val invs = qpInversesMap(n.getPrettyMetadata._1)._2
        val notWildcardPerm: ast.Exp = p match {
          case _:ast.WildcardPerm => ast.FullPerm()()
          case p => p
        }
        val proxyFa = ast.Forall(forall.variables, Seq(), ast.And(cond, ast.GtCmp(notWildcardPerm, ast.IntLit(0)())())())()
        val Seq(tFa) = expressionTranslator.translatePrecondition(program, Seq(proxyFa), this)
        
        val is = tFa.asInstanceOf[Quantification].vars
        mergeDoms(dm, Map(f -> (r => is.foldLeft(tFa.asInstanceOf[Quantification].body)((body, i) => body.replace(i, App(invs(i), r +: axiomArguments))))))
      }
      case n@QuantifiedPermissionAssertion(forall, cond, ast.PredicateAccessPredicate(ast.PredicateAccess(args, pred), p: ast.Exp)) => {
        val invs = qpInversesMap(n.getPrettyMetadata._1)._2

        val notWildcardPerm: ast.Exp = p match {
          case _:ast.WildcardPerm => ast.FullPerm()()
          case p => p
        }
        val proxyFa = ast.Forall(forall.variables, Seq(), ast.And(cond, ast.GtCmp(notWildcardPerm, ast.IntLit(0)())())())()
        val Seq(tFa) = expressionTranslator.translatePrecondition(program, Seq(proxyFa), this)
        
        val is = tFa.asInstanceOf[Quantification].vars
        mergeDoms(dm, Map(program.findPredicate(pred) -> (l => is.foldLeft(tFa.asInstanceOf[Quantification].body)((body, i) => body.replace(i, App(invs(i), l +: axiomArguments))))))
      }

      // Combined assertions that allow pure sub assertions
      case ast.And(e1,e2) => mergeDoms(go(e1, dm), go(e2, dm))
      case ast.CondExp(cond,e1,e2) =>
        val tCond = expressionTranslator.translatePrecondition(program, Seq(cond), this).head
        val e1Dom = getDomMap(e1)
        val e2Dom = getDomMap(e2)
        mergeDoms(dm, mergeDoms(e1Dom, e2Dom, Ite(tCond, _, _)))
      case ast.Implies(e1, e2) =>
        val tE1 = expressionTranslator.translatePrecondition(program, Seq(e1), this).head
        val e2Dom = getDomMap(e2)
        mergeDoms(dm, mergeDoms(e2Dom, Map.empty, Ite(tE1, _, _)))
      /** TODO
      case ast.InhaleExhaleExp(e1, e2) => {

      }
      */

      // Any other assertion should be pure
      case a => if (a.isPure)
                  Map.empty
                else
                  sys.error("Cannot getDomMap() of " + a.toString)
    }

    val emptyDomMap : Map[ast.Resource, Term => Term] = toMap( program.fields.zip(Seq.fill(program.fields.length){(_:Term) => False()})
                          ++ program.predicates.zip(Seq.fill(program.predicates.length){(_:Term) => False()}))
    go(pre, emptyDomMap)
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

  private def generateNestedDefinitionalAxioms: InsertionOrderedSet[Term] = {
    val nested = (
    //   freshFieldInvs.flatMap(_.definitionalAxioms)
    //++ freshFvfsAndDomains.flatMap (fvfDef => fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
         freshArps.map(_._2))

    // Filter out nested definitions that contain free variables.
    // This should not happen, but currently can, due to bugs in the function axiomatisation code.
    // Fixing these bugs with the current way functions are axiomatised will be very difficult,
    // but they should be resolved with Mauro's current work on heap snapshots.
    // Once his changes are merged in, the commented warnings below should be turned into errors.
    nested.filter(term => {
      val freeVars = term.freeVariables -- axiomArguments

    //if (freeVars.nonEmpty) {
    //  val messageText = (
    //      s"Found unexpected free variables $freeVars "
    //    + s"in term $term during axiomatisation of function "
    //    + s"${programFunction.name}")
    //
    //  reporter report InternalWarningMessage(messageText)
    //  logger warn messageText
    //}

      freeVars.isEmpty
    })
  }

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

      Some(Forall(axiomArguments, body, Trigger(limitedFunctionApplication), s"postAxiom [${function.id.name}]"))
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

    // predicateAccesses initially contains all predicate instances unfolded by the function
    var predicateAccesses: Seq[ast.PredicateAccess] =
      if (recursiveCallsAndUnfoldings.isEmpty)
        Vector.empty
      else
        outerUnfoldings map (_.acc.loc)

    // // Could add predicate instances from precondition as well, but currently not done (also not in Carbon)
    // predicateAccesses ++=
    //   programFunction.pres.flatMap(_.shallowCollect { case predAcc: ast.PredicateAccess => predAcc })

    // Only keep predicate instances whose arguments do not contain free variables
    predicateAccesses = {
      val functionArguments: Seq[ast.AbstractLocalVar] = programFunction.formalArgs.map(_.localVar)

      predicateAccesses.filter(predAcc =>
        predAcc.args.forall(arg => ast.utility.Expressions.freeVariablesExcluding(arg, functionArguments).isEmpty))
    }

    toMap(predicateAccesses.map(predAcc => {
      val predicate = program.findPredicate(predAcc.predicateName)
      val triggerFunction = predicateData(predicate).triggerFunction

      /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
      val tArgs = expressionTranslator.translatePrecondition(program, predAcc.args, this)
      val args = (
        PHeapLookupPredicate(predAcc.predicateName, functionSupporter.axiomSnapshotVariable, tArgs)
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
      val body = And(nestedDefinitionalAxioms ++ List(Implies(pre, And(functionApplication === translatedBody))))
      val allTriggers = (
           Seq(Trigger(functionApplication))
        ++ predicateTriggers.values.map(pt => Trigger(Seq(triggerFunctionApplication, pt))))

      Forall(axiomArguments, body, allTriggers, s"definitionalAxiom [${function.id.name}]")})
  }
}
