// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import scala.collection.mutable
import viper.silicon.state.terms._

package object utils {

  // Applies a simple search-and-replace strategy to project heap dependencies of a trigger to quantified variables
  // Splits the quantifier per trigger
  def makeTriggersHeapIndependent(q : Quantification, fresh: (String, Sort) => Var) : Seq[Quantification] = {

    /**
     * [2020-10-12 Mauro]
     *
     * The two functions below are heavily coupled and need to match up in their cases.
     * There are probably better ways of doing this, potentially using `deepCollect` and `transform`.
     * Also, I did not try to make this implementation as complete as possible,
     * so there might still be cases where a heap dependency is not projected out of the quantifier.
     **/
    def computeHeapDeps(t: Term) : Seq[Term] = t match {
      case App(HeapDepFun(_,_,_), args) => args.flatMap(computeHeapDeps)
      case PHeapLookupField(f, s, h, at) => Seq(t)
      case _ if t.sort == sorts.PHeap => Seq(t)
      case _ => Seq()
    }

    def replaceHeapDeps(t: Term, m: Map[Term, Var]) : Term = t match {
      case App(f@HeapDepFun(_,_,_), args) => App(f, args.map(replaceHeapDeps(_,m)))
      case PHeapLookupField(f, s, h, at) => (m get t).get
      case _ => m.getOrElse(t, t)
    }

    /**
     * [2020-10-12 Mauro]
     *
     * In order to reduce the amount of transformation and unnecessary quantifier splitting,
     * one could keep all heap-independent triggers under one quantifier.
     * This version here will simply compute an empty heap dependency Map but split the quantifier per trigger anyway.
     * My assumption is that these two alternatives behave exactly the same way.
     **/
    q.triggers
      // : Seq[Trigger]
      // Find heap dependencies for each trigger separately
      .map(({ case Trigger(ts) => (ts, ts.flatMap(computeHeapDeps))}))
      .distinct
      // : Seq[(Trigger, Seq[Term])]
      // Map all heap dependencies to fresh variables
      .map({ case (ts, deps) => (ts, deps.map(t => (t, fresh("proj", t.sort))).toMap)})
      // : Seq[(Trigger, Map[Term, Var])]
      // For each trigger, create a new quantifier where all heap dependencies are replaced with the new variables
      .map({ case (ts, m) => Quantification(q.q,
              q.vars ++ m.values.toSeq,

              /**
               * [2020-07-15 Mauro]
               *
               * This would be the premised version which narrows down all projected terms back to their original values (untested):
               
                 Implies( And(m.map({ case (t,p) => t === p})), q.body )

               * This could be needed to restore the original triggering behavior on the Viper level,
               * i.e. how user-provided, heap-dependent triggers behave.
               * Soundness should not be affected by this since it can only result in less obtained equalities.
               * Performance is probably not affected significantly either, since the quantifier can still be instantiated with an arbitrary term.
               **/

              q.body,
              Seq(Trigger(ts.map(replaceHeapDeps(_,m)))), 
              q.name,
              q.isGlobal)})

  }

  /** Note: the method accounts for `ref` occurring in `σ`, i.e. it will not generate the
    * unsatisfiable constraint `ref != ref`.
    */
  def computeReferenceDisjointnesses(s: State, ref: Term)
                                    : Seq[Term] = {

    val refs = mutable.HashSet[Term]()
    val refSets = mutable.HashSet[Term]()
    val refSeqs = mutable.HashSet[Term]()

    def collect(t: Term) {
      t.sort match {
        case sorts.Ref => if (t != ref) refs += t
        case sorts.Set(sorts.Ref) => refSets += t
        case sorts.Seq(sorts.Ref) => refSeqs += t
        case _ =>
      }
    }

    /* Collect all Ref/Set[Ref]/Seq[Ref]-typed values from the store */
    s.g.values.values foreach collect

    /* Collect all Ref/Set[Ref]/Seq[Ref]-typed terms from heap chunks */
    s.h.values.foreach {
      case bc: BasicChunk =>
        bc.args foreach collect
        collect(bc.snap)
      case qch: QuantifiedFieldChunk =>
        /* Terms from quantified chunks contain the implicitly quantified receiver `?r`,
         * hence, they can only be used under quantifiers that bind `?r`.
         * An exception are quantified chunks that (definitely) provide permissions to
         * a single location (i.e. for a single receiver) only.
         */
        qch.singletonRcvr.foreach(rcvr => {
          collect(rcvr)
          collect(qch.valueAt(rcvr))
        })
      case _ =>
    }

    val disjointnessAssumptions = mutable.ListBuffer[Term]()

    refs foreach (r => disjointnessAssumptions += (ref !== r))
    refSets foreach (rs => disjointnessAssumptions += Not(SetIn(ref, rs)))
    refSeqs foreach (rs => disjointnessAssumptions += Not(SeqIn(rs, ref)))

    disjointnessAssumptions.result()
  }

  def subterms(t: Term): Seq[Term] = t match {
    case _: Symbol | _: Literal | _: MagicWandChunkTerm => Nil
    case op: BinaryOp[Term@unchecked] => List(op.p0, op.p1)
    case op: UnaryOp[Term@unchecked] => List(op.p)
    case ite: Ite => List(ite.t0, ite.t1, ite.t2)
    case and: And => and.ts
    case or: Or => or.ts
    case _: PermLiteral => Nil
    case fp: FractionPerm => List(fp.n, fp.d)
    case ivp: IsValidPermVar => List(ivp.v)
    case irp: IsReadPermVar => List(irp.v, irp.ub)
    case app: Application[_] => app.args
    case sr: SeqRanged => List(sr.p0, sr.p1)
    case ss: SeqSingleton => List(ss.p)
    case su: SeqUpdate => List(su.t0, su.t1, su.t2)
    case ss: SingletonSet => List(ss.p)
    case ss: SingletonMultiset => List(ss.p)
    case sw: SortWrapper => List(sw.t)
    case d: Distinct => Seq.empty // d.ts.toList
    case q: Quantification => q.vars ++ List(q.body) ++ q.triggers.flatMap(_.p)
    case l: Let =>
      val (vs, ts) = l.bindings.toSeq.unzip
      vs ++ ts :+ l.body
    case PHeapEqual(h1, h2) => h1 :: h2 :: Nil
    case PHeapCombine(h1, h2) => h1 :: h2 :: Nil
    case PHeapLookupField(_, _, h, at) => h :: at :: Nil
    case PHeapFieldDomain(_,h) => h :: Nil
    case PHeapPredicateDomain(_, h) => Seq(h)
    case PHeapPredicateLoc(_, args) => args
    case PHeapPredicateLocInv(_,_,_,x) => Seq(x)
    case PHeapLookupPredicate(_, h, args) => Seq(h) ++ args
    case PHeapRemovePredicate(_, h, args) => Seq(h) ++ args
    case PHeapUnfoldPredicate(_, h, args, rc) => Seq(h) ++ args ++ Seq(rc)
    case PHeapSingletonField(_, x, v) => x :: v :: Nil
    case PHeapSingletonPredicate(_, args, h) => Seq(h) ++ args 
    case PHeapRestrict(_, h, args) => Seq(h) ++ args
    case Domain(_, fvf) => fvf :: Nil
    case Lookup(_, fvf, at) => fvf :: at :: Nil
    case PHeapToFVF(_, _, h) => h :: Nil
    case FVFToPHeap(_, fvf) => fvf :: Nil
    case PHeapLHS(h) => h :: Nil
    case PHeapRHS(h) => h :: Nil
    case PHeapMWS(h1,h2) => h1 :: h2 :: Nil
    case PermLookup(_, pm, at) => pm :: at :: Nil
    case PredicatePermLookup(_, pm, args) => Seq(pm) ++ args
    case FieldTrigger(_, fvf, at) => fvf :: at :: Nil
    case PredicateTrigger(_, psf, args) => psf +: args

  }

  /** @see [[viper.silver.ast.utility.Transformer.simplify()]] */
  def transform[T <: Term](term: T,
                           pre: PartialFunction[Term, Term] = PartialFunction.empty)
                          (recursive: Term => Boolean = !pre.isDefinedAt(_),
                           post: PartialFunction[Term, Term] = PartialFunction.empty)
                          : T = {

    def go[D <: Term](term: D): D = transform(term, pre)(recursive, post)

    def goTriggers(trigger: Trigger) = Trigger(trigger.p map go)

    def recurse(term: Term): Term = term match {
      case _: Var | _: Function | _: Literal | _: MagicWandChunkTerm | _: Distinct => term

      case Quantification(quantifier, variables, body, triggers, name, isGlobal) =>
        Quantification(quantifier, variables map go, go(body), triggers map goTriggers, name, isGlobal)

      case Plus(t0, t1) => Plus(go(t0), go(t1))
      case Minus(t0, t1) => Minus(go(t0), go(t1))
      case Times(t0, t1) => Times(go(t0), go(t1))
      case Div(t0, t1) => Div(go(t0), go(t1))
      case Mod(t0, t1) => Mod(go(t0), go(t1))
      case Not(t) => Not(go(t))
      case Or(ts) => Or(ts map go : _*)
      case And(ts) => And(ts map go : _*)
      case Implies(t0, t1) => Implies(go(t0), go(t1))
      case Iff(t0, t1) => Iff(go(t0), go(t1))
      case Ite(t0, t1, t2) => Ite(go(t0), go(t1), go(t2))
      case BuiltinEquals(t0, t1) =>
        val t0New = go(t0)
        val t1New = go(t1)
        /* Rewriting equalities is potentially ambiguous: if the sort of the arguments of a
         * built-in equality changes from a primitive to a non-primitive sort, e.g. from Int
         * to Set[E], then users might or might not expect that the built-in equality is
         * replaced by the sort-specific, custom equality.
         *
         * For now, such potentially ambiguous transformations are rejected by the following
         * assertions.
         */
        assert(t0New.sort == t0.sort, s"Unexpected sort change: from ${t0.sort} to ${t0New.sort}")
        BuiltinEquals(t0New, t1New)
      case CustomEquals(t0, t1) =>
        val t0New = go(t0)
        val t1New = go(t1)
        /* See comments for built-in equality.
         *
         * Difference here: instead of creating a new CustomEquality instance directly, the
         * factory method Equals.apply could be used to create, depending on the new sort of the
         * arguments, either a built-in or a custom equality.
         */
        assert(t0New.sort == t0.sort, s"Unexpected sort change: from ${t0.sort} to ${t0New.sort}")
        CustomEquals(t0New, t1New)
      case Less(t0, t1) => Less(go(t0), go(t1))
      case AtMost(t0, t1) => AtMost(go(t0), go(t1))
      case Greater(t0, t1) => Greater(go(t0), go(t1))
      case AtLeast(t0, t1) => AtLeast(go(t0), go(t1))
      case _: PermLiteral => term
      case FractionPerm(n, d) => FractionPerm(go(n), go(d))
      case IsValidPermVar(v) => IsValidPermVar(go(v))
      case IsReadPermVar(v, ub) => IsReadPermVar(go(v), go(ub))
      case PermTimes(p0, p1) => PermTimes(go(p0), go(p1))
      case IntPermTimes(p0, p1) => IntPermTimes(go(p0), go(p1))
      case PermIntDiv(p0, p1) => PermIntDiv(go(p0), go(p1))
      case PermPlus(p0, p1) => PermPlus(go(p0), go(p1))
      case PermMinus(p0, p1) => PermMinus(go(p0), go(p1))
      case PermLess(p0, p1) => PermLess(go(p0), go(p1))
      case PermAtMost(p0, p1) => PermAtMost(go(p0), go(p1))
      case PermMin(p0, p1) => PermMin(go(p0), go(p1))
      case App(f, ts) => App(f, ts map go)
      case SeqRanged(t0, t1) => SeqRanged(go(t0), go(t1))
      case SeqSingleton(t) => SeqSingleton(go(t))
      case SeqAppend(t0, t1) => SeqAppend(go(t0), go(t1))
      case SeqDrop(t0, t1) => SeqDrop(go(t0), go(t1))
      case SeqTake(t0, t1) => SeqTake(go(t0), go(t1))
      case SeqLength(t) => SeqLength(go(t))
      case SeqAt(t0, t1) => SeqAt(go(t0), go(t1))
      case SeqIn(t0, t1) => SeqIn(go(t0), go(t1))
      case SeqUpdate(t0, t1, t2) => SeqUpdate(go(t0), go(t1), go(t2))
      case SingletonSet(t) => SingletonSet(go(t))
      case SetAdd(t0, t1) => SetAdd(go(t0), go(t1))
      case SetUnion(t0, t1) => SetUnion(go(t0), go(t1))
      case SetIntersection(t0, t1) => SetIntersection(go(t0), go(t1))
      case SetSubset(t0, t1) => SetSubset(go(t0), go(t1))
      case SetDifference(t0, t1) => SetDifference(go(t0), go(t1))
      case SetIn(t0, t1) => SetIn(go(t0), go(t1))
      case SetCardinality(t) => SetCardinality(go(t))
      case SetDisjoint(t0, t1) => SetDisjoint(go(t0), go(t1))
      case SingletonMultiset(t) => SingletonMultiset(go(t))
      case MultisetUnion(t0, t1) => MultisetUnion(go(t0), go(t1))
      case MultisetIntersection(t0, t1) => MultisetIntersection(go(t0), go(t1))
      case MultisetSubset(t0, t1) => MultisetSubset(go(t0), go(t1))
      case MultisetDifference(t0, t1) => MultisetDifference(go(t0), go(t1))
      case MultisetCardinality(t) => MultisetCardinality(go(t))
      case MultisetCount(t0, t1) => MultisetCount(go(t0), go(t1))
      case MultisetAdd(t1, t2) => MultisetAdd(go(t1), go(t2))
      case MagicWandSnapshot(lhs, rhs) => MagicWandSnapshot(go(lhs), go(rhs))
      case Combine(t0, t1) => Combine(go(t0), go(t1))
      case First(t) => First(go(t))
      case Second(t) => Second(go(t))
      case SortWrapper(t, s) => SortWrapper(go(t), s)
//      case Distinct(ts) => Distinct(ts map go)
      case Let(bindings, body) => Let(bindings map (p => go(p._1) -> go(p._2)), go(body))
      case Domain(f, fvf) => Domain(f, go(fvf))
      case Lookup(f, fvf, at) => Lookup(f, go(fvf), go(at))
      case PermLookup(field, pm, at) => PermLookup(field, go(pm), go(at))
      case FieldTrigger(f, fvf, at) => FieldTrigger(f, go(fvf), go(at))

      case PredicatePermLookup(predname, pm, args) => PredicatePermLookup(predname, go(pm), args map go)
      case PredicateTrigger(p, psf, args) => PredicateTrigger(p, go(psf), args map go)

      case PHeapEqual(h1, h2) => PHeapEqual( go(h1), go(h2))
      case PHeapCombine(h1, h2) => PHeapCombine( go(h1), go(h2))
      case PHeapLookupField(f, s, h, at) => PHeapLookupField(f, s, go(h), go(at))
      case PHeapPredicateLoc(p, args) => PHeapPredicateLoc(p,args map go)
      case PHeapPredicateLocInv(p,i,s,x) => PHeapPredicateLocInv(p,i,s, go(x))
      case PHeapPredicateDomain(p, h) => PHeapPredicateDomain(p, go(h))
      case PHeapLookupPredicate(p, h, args) => PHeapLookupPredicate(p, go(h), args map go)
      case PHeapRemovePredicate(p, h, args) => PHeapRemovePredicate(p, go(h), args map go)
      case PHeapUnfoldPredicate(p, h, args, rc) => PHeapUnfoldPredicate(p, go(h), args map go, go(rc))
      case PHeapSingletonField(f, x, v) => PHeapSingletonField(f, go(x), go(v))
      case PHeapSingletonPredicate(p, args, h) => PHeapSingletonPredicate(p, args map go, go(h))
      case PHeapRestrict(g, h, args) => PHeapRestrict(g, go(h), args map go)

      case PHeapToFVF(f, fs, h) => PHeapToFVF(f,fs,go(h))
      case FVFToPHeap(f, fvf) => FVFToPHeap(f, go(fvf))

      case PHeapLHS(h) => PHeapLHS(go(h))
      case PHeapRHS(h) => PHeapRHS(go(h))
      case PHeapMWS(h1,h2) => PHeapMWS(go(h1), go(h2))
    }

    val beforeRecursion = pre.applyOrElse(term, identity[Term])

    val afterRecursion =
      if (recursive(term)) recurse(beforeRecursion)
      else beforeRecursion

    post.applyOrElse(afterRecursion, identity[Term]).asInstanceOf[T]
  }
}
