// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.rules.predicateSupporter
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{SortDecl, sorts}
import viper.silicon.state.{Identifier, MagicWandIdentifier}
import viper.silicon.state.terms._

trait PHeapsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

class DefaultPHeapsContributor(preambleReader: PreambleReader[String, String],
                               symbolConverter: SymbolConverter,
                               termConverter: TermConverter[String, String, String],
                               config: Config)
    extends PHeapsContributor[sorts.FieldValueFunction, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  private var astAxioms: Iterable[Term] = Seq.empty
  private var astDecls: Iterable[Decl] = Seq.empty

  private def fieldSubstitutions(f: ast.Field) : Map[String, String] = {
    val sort = symbolConverter.toSort(f.typ)
    val id = f.name
    Map(
      "$FLD$" -> id,
      "$S$" -> termConverter.convert(sort)
    )
  }

  private def predicateSubstitutions(p: ast.Predicate) : Map[String, String] = {
    val pArgs_q = (p.formalArgs map (a => 
	    "(" + p.name + "_" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
    val pArgs = (p.formalArgs map (a => p.name + "_" + a.name)).mkString(" ")
    val argSorts = (p.formalArgs map (a => termConverter.convert(symbolConverter.toSort(a.typ)))).mkString(" ")
    val id = p.name
    val pLoc = if (p.formalArgs.length > 0) {
      "(PHeap.loc_" + p.name + " " + pArgs + ")"
    } else {
      "PHeap.loc_" + p.name
    }

    Map(
      "$PRD$" -> id,
      "$PRD_ARGS_S$" -> argSorts,
      "$PRD_ARGS_Q$" -> pArgs_q,
      "$PRD_ARGS$" -> pArgs,
      "$PRD_LOC$" -> pLoc,
    )
  }

  private def wandSubstitutions(wand: ast.MagicWand, program: ast.Program) : Map[String, String] = {
    val id = MagicWandIdentifier(wand, program).toString
    val formalArgs = (wand.subexpressionsToEvaluate(program).zipWithIndex map ({ case (a, i) => 
      val argName = f"arg${i}" 
      Var(Identifier(argName), symbolConverter.toSort(a.typ))
	  }))
    val mwArgs_q = formalArgs.map(a => 
	    "(" + id + "_" + a.id.name + " " + termConverter.convert(a.sort) + ")"
	  ).mkString(" ")
    val mwArgs = (formalArgs map (a => id + "_" + a.id.name)).mkString(" ")
    val argSorts = (formalArgs map (a => termConverter.convert(a.sort))).mkString(" ")
    val mwLoc = if (formalArgs.length > 0) {
      "(PHeap.loc_" + id + " " + mwArgs + ")"
    } else {
      "PHeap.loc_" + id
    }

    Map(
      "$PRD$" -> id,
      "$PRD_ARGS_S$" -> argSorts,
      "$PRD_ARGS_Q$" -> mwArgs_q,
      "$PRD_ARGS$" -> mwArgs,
      "$PRD_LOC$" -> mwLoc,
    )
  }

  private def addKeySuffix(m : Map[String, String], s : String) : Map[String, String] = m.map {
    case (k, v) => k.substring(0, k.length - 1) + s + "$" -> v
  }

  /* Lifetime */

  def reset() {
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop() {}
  def start() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    collectedFunctionDecls =
      generatePHeapFunctions ++
      generateFieldFunctionDecls(program) ++
      generatePredicateFunctionDecls(program)
    collectedAxioms =
      field_lookup_combine(program) ++ 
      field_dom_combine(program) ++
      pred_dom_combine(program) ++
      pred_lookup_combine(program) ++
      symmetry_combine() ++
      predicateSingletonFieldDomains(program) ++
      predicateSingletonPredicateDomains(program) ++
      fieldSingletonPredicateDomains(program) ++
      fieldSingletonFieldDomains(program)
    astDecls =
      predicate_loc_inv_func_decls(program)
    astAxioms =
      extensional_equality(program) ++
      predicate_loc_inv_func_axioms(program)
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generatePHeapFunctions(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pheap_functions.smt2"
      Seq(("basic pheap functions", preambleReader.readPreamble(templateFile)))    
  }

  def generateFieldFunctionDecls(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_functions.smt2"

    program.fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"$templateFile [${f.name}]", declarations)
    })
  }

  def generatePredicateFunctionDecls(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_functions.smt2"

    (program.predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })) ++
    (program.magicWandStructures map (mw => {
      val declarations = preambleReader.readParametricPreamble(templateFile, wandSubstitutions(mw, program))
      (s"$templateFile [${MagicWandIdentifier(mw, program)}]", declarations)
    }))
  }

  def pred_lookup_combine(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pred_lookup_combine.smt2"

    (program.predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })) ++
    (program.magicWandStructures map (mw => {
      val declarations = preambleReader.readParametricPreamble(templateFile, wandSubstitutions(mw, program))
      (s"$templateFile [${MagicWandIdentifier(mw, program)}]", declarations)
    }))
  }

  def field_lookup_combine(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_lookup_combine.smt2"

    program.fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"PHeap.field_lookup_combine[${f.name}]", declarations)
    })
  }

  def field_dom_combine(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_dom_combine.smt2"

    program.fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"PHeap.field_dom_combine[${f.name}]", declarations)
    })
  }

  def pred_dom_combine(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pred_dom_combine.smt2"

    (program.predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"PHeap.pred_dom_combine[${p.name}]", declarations)
    })) ++
    (program.magicWandStructures map (mw => {
      val declarations = preambleReader.readParametricPreamble(templateFile, wandSubstitutions(mw, program))
      (s"PHeap.pred_dom_combine [${MagicWandIdentifier(mw, program)}]", declarations)
    }))
  }
  
  def symmetry_combine(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/symmetry_combine.smt2"
    Seq((s"PHeap.symmetry_combine", preambleReader.readPreamble(templateFile)))
  }

  def predicate_loc_inv_func_decls(program: ast.Program): Iterable[FunctionDecl] = {
    (program.predicates.flatMap(p => {
      p.formalArgs.zipWithIndex.map({ case (a,i) => 
        val id = predicateSupporter.inverseLocFunctionId(p.name, i)
        val a_sort = symbolConverter.toSort(a.typ)
        FunctionDecl(Fun(id, Seq(sorts.Loc), a_sort))
      })
    })) ++
    (program.magicWandStructures.flatMap(mw => {
      val formalArgSorts = mw.subexpressionsToEvaluate(program) map (a => symbolConverter.toSort(a.typ))
      formalArgSorts.zipWithIndex.map({ case (asort,i) => 
        val id = predicateSupporter.inverseLocFunctionId(MagicWandIdentifier(mw, program).toString, i)
        FunctionDecl(Fun(id, Seq(sorts.Loc), asort))
      })
    }))
  }

  def predicate_loc_inv_func_axioms(program: ast.Program): Iterable[Term] = {
    program.predicates.flatMap(p => p.formalArgs.zipWithIndex.flatMap({ case (a,i) =>
      val a_sort = symbolConverter.toSort(a.typ)
      val pArgs = p.formalArgs.map(a => Var(Identifier(a.name), symbolConverter.toSort(a.typ)))
      val inv1 = Forall( pArgs
                       , PHeapPredicateLocInv(p.name, i, a_sort, PHeapPredicateLoc(p.name, pArgs)) === pArgs(i)
                       , Seq(Trigger(PHeapPredicateLocInv(p.name, i, a_sort, PHeapPredicateLoc(p.name, pArgs))))
                       )
      val l = Var(Identifier("l"), sorts.Loc)
      val inv2 = Forall( l
                       , PHeapPredicateLoc(p.name, pArgs.zipWithIndex.map({ case (a,i) => PHeapPredicateLocInv(p.name, i, a.sort, l)})) === l
                       , Seq(Trigger(PHeapPredicateLoc(p.name, pArgs.zipWithIndex.map({ case (a,i) => PHeapPredicateLocInv(p.name, i, a.sort, l)}))))
                       )
      Seq(inv1, inv2)
    })) ++
    program.magicWandStructures.flatMap(mw => {
      val formalArgs = mw.subexpressionsToEvaluate(program).zipWithIndex map ({ case (a,i) => Var(Identifier(f"arg$i") ,symbolConverter.toSort(a.typ)) })
      val mwid = MagicWandIdentifier(mw, program).toString

      formalArgs.zipWithIndex flatMap ({ case (a,i) => {
        val inv1 = Forall( formalArgs
                         , PHeapPredicateLocInv(mwid, i, a.sort, PHeapPredicateLoc(mwid, formalArgs)) === formalArgs(i)
                         , Seq(Trigger(PHeapPredicateLocInv(mwid, i, a.sort, PHeapPredicateLoc(mwid, formalArgs))))
                         )
        val l = Var(Identifier("l"), sorts.Loc)
        val inv2 = Forall( l
                         , PHeapPredicateLoc(mwid, formalArgs.zipWithIndex.map({ case (a,i) => PHeapPredicateLocInv(mwid, i, a.sort, l)})) === l
                         , Seq(Trigger(PHeapPredicateLoc(mwid, formalArgs.zipWithIndex.map({ case (a,i) => PHeapPredicateLocInv(mwid, i, a.sort, l)}))))
                         )
        Seq(inv1, inv2)
      }})
    })
  }

  def extensional_equality (program: ast.Program): Iterable[Term] = {
    val h1 = Var(Identifier("h1"), sorts.PHeap)
    val h2 = Var(Identifier("h2"), sorts.PHeap)

    val equalOnPredicates = program.predicates.foldLeft[Term](True())((ax, p) => And(ax, equalOnPred(p.name, h1, h2)))
    val equalOnWands = program.magicWandStructures.foldLeft[Term](True())((ax, mw) => And(ax, equalOnPred(MagicWandIdentifier(mw, program).toString, h1, h2)))
    val equalOnFields = program.fields.foldLeft[Term](True())((ax, f) => And(ax, equalOnField(f, h1, h2)))

    Seq(Forall( Seq(h1, h2)
          , Implies(And(equalOnFields, equalOnPredicates, equalOnWands), PHeapEqual(h1,h2))
          , Trigger(PHeapEqual(h1, h2))))
  }

  private def equalOnField(f: ast.Field, h1: Term, h2: Term) : Term = {
    val r = Var(Identifier("r"), sorts.Ref)
    val fSort = symbolConverter.toSort(f.typ)
    And( SetEqual(PHeapFieldDomain(f.name, h1), PHeapFieldDomain(f.name, h2))
        , Forall( Seq(r)
                , Implies( SetIn(r, PHeapFieldDomain(f.name, h1))
                        , PHeapLookupField(f.name, fSort, h1, r) === PHeapLookupField(f.name, fSort, h2, r))
                , Seq( Trigger(Seq(PHeapLookupField(f.name, fSort, h1, r), PHeapLookupField(f.name, fSort, h2, r))))
                )
    )
  }

  private def equalOnPred(id: String, h1: Term, h2: Term) : Term = {
    val l = Var(Identifier("l"), sorts.Loc)
    // Note that we do not directly use 'PHeapLookupPredicate',
    // since that already abstracts away from the 'Loc's and takes the actual arguments instead
    val lk1 = App(Fun(Identifier("PHeap.lookup_" ++ id), Seq(sorts.PHeap, sorts.Loc), sorts.PHeap), Seq(h1, l))
    val lk2 = App(Fun(Identifier("PHeap.lookup_" ++ id), Seq(sorts.PHeap, sorts.Loc), sorts.PHeap), Seq(h2, l))
    And( SetEqual(PHeapPredicateDomain(id, h1), PHeapPredicateDomain(id, h2))
        , Forall( Seq(l)
                , Implies( SetIn(l, PHeapPredicateDomain(id, h1))
                         , PHeapEqual(lk1, lk2))
                , Seq(Trigger(Seq(lk1, lk2))))
    )
  }

  def predicateSingletonFieldDomains(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_field_domain.smt2"

    (program.predicates flatMap (p => {
      program.fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"predicate_singleton_field_domain (${p.name}, ${f.name})", declarations)
      })
    })) ++
    (program.magicWandStructures flatMap (mw => {
      program.fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ wandSubstitutions(mw, program))
        (s"predicate_singleton_field_domain (${MagicWandIdentifier(mw, program)}, ${f.name})", declarations)
      })
    }))
  }

  def fieldSingletonFieldDomains(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_field_domain.smt2"
    program.fields flatMap (f2 => {
      program.fields map (f => {
        if (f.name == f2.name) {
          ("", Seq())
        } else {
          val substitutions = fieldSubstitutions(f) ++ addKeySuffix(fieldSubstitutions(f2), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"field_singleton_field_domain (${f.name}, ${f2.name})", declarations)
        }
      })
    })
  }

  def fieldSingletonPredicateDomains(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_predicate_domain.smt2"

    program.predicates flatMap (p => {
      program.fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"field_singleton_predicate_domain (${p.name}, ${f.name})", declarations)
      })
    })
    program.magicWandStructures flatMap (mw => {
      program.fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ wandSubstitutions(mw, program))
        (s"field_singleton_predicate_domain (${MagicWandIdentifier(mw, program)}, ${f.name})", declarations)
      })
    })
  }

  def predicateSingletonPredicateDomains(program: ast.Program): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_predicate_domain.smt2"

    program.predicates flatMap (p => {
      val pred_id = p.name
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val pArgs_q = (p.formalArgs map (a => 
          "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
      )).mkString(" ")
      (program.predicates map (p2 => {
        if (p.name == p2.name) {
          ("", Seq())
        } else {
          val substitutions = predicateSubstitutions(p) ++ addKeySuffix(predicateSubstitutions(p2), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"predicate_singleton_predicate_domain (${p.name}, ${p2.name})", declarations)
        }
      })) ++
      (program.magicWandStructures map (mw => {
          val substitutions = predicateSubstitutions(p) ++ addKeySuffix(wandSubstitutions(mw, program), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"predicate_singleton_predicate_domain (${p.name}, ${MagicWandIdentifier(mw, program)})", declarations)
      }))
    })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[sorts.FieldValueFunction] = InsertionOrderedSet.empty

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    Seq(sorts.PHeap, sorts.Loc) foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    astDecls.map(d => sink.declare(d))
    astAxioms.map(ax => sink.assume(ax))
    emitPreambleLines(sink, collectedAxioms)
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
