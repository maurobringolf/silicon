// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{SortDecl, sorts}
import viper.silicon.state.Identifier
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
      generateFieldFunctionDecls(program.fields) ++
      generatePredicateFunctionDecls(program.predicates)
    collectedAxioms =
      field_lookup_combine(program.fields) ++ 
      field_dom_combine(program.fields) ++
      pred_dom_combine(program.predicates) ++
      pred_lookup_combine(program.predicates) ++
      symmetry_combine() ++
      predicateSingletonFieldDomains(program.predicates, program.fields) ++
      predicateSingletonPredicateDomains(program.predicates) ++
      fieldSingletonPredicateDomains(program.predicates, program. fields) ++
      fieldSingletonFieldDomains(program.fields)
    astAxioms = extensional_equality(program.predicates, program.fields, program.functions)
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

  def generateFieldFunctionDecls(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_functions.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"$templateFile [${f.name}]", declarations)
    })
  }

  def generatePredicateFunctionDecls(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_functions.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })
  }

  def pred_lookup_combine(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pred_lookup_combine.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"$templateFile [${p.name}]", declarations)
    })
  }

  def field_lookup_combine(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_lookup_combine.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"PHeap.field_lookup_combine[${f.name}]", declarations)
    })
  }

  def field_dom_combine(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_dom_combine.smt2"

    fields map (f => {
      val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f))
      (s"PHeap.field_dom_combine[${f.name}]", declarations)
    })
  }

  def pred_dom_combine(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pred_dom_combine.smt2"

    predicates map (p => {
      val declarations = preambleReader.readParametricPreamble(templateFile, predicateSubstitutions(p))
      (s"PHeap.pred_dom_combine[${p.name}]", declarations)
    })
  }
  
  def symmetry_combine(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/symmetry_combine.smt2"
    Seq((s"PHeap.symmetry_combine", preambleReader.readPreamble(templateFile)))
  }

  // TODO: Extend the meta syntax as needed to write this in SMT-LIB
  def extensional_equality( predicates: Seq[ast.Predicate]
                          , fields: Seq[ast.Field]
                          , functions: Seq[ast.Function]
                          ): Iterable[Term] = {
    val h1 = Var(Identifier("h1"), sorts.PHeap)
    val h2 = Var(Identifier("h2"), sorts.PHeap)
    val h3 = Var(Identifier("h3"), sorts.PHeap)
    val r = Var(Identifier("r"), sorts.Ref)
    val pHeap_equal = Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool)

    // TODO
    def equalOnPred(p: ast.Predicate) : Term = {
      val l = Var(Identifier("l"), sorts.Loc)
      val lk1 = App(Fun(Identifier("PHeap.lookup_" ++ p.name), Seq(sorts.PHeap, sorts.Loc), sorts.PHeap), Seq(h1, l))
      val lk2 = App(Fun(Identifier("PHeap.lookup_" ++ p.name), Seq(sorts.PHeap, sorts.Loc), sorts.PHeap), Seq(h2, l))
      And( SetEqual(PHeapPredicateDomain(p.name, h1), PHeapPredicateDomain(p.name, h2))
         , Forall( Seq(l)
                 , Implies( SetIn(l, PHeapPredicateDomain(p.name, h1))
                          , App(pHeap_equal, Seq(lk1, lk2)))
                 , Seq(Trigger(Seq(lk1, lk2)))
         )
      )
    }

    def equalOnField(f: ast.Field) : Term = {
      val fSort = symbolConverter.toSort(f.typ)
      And( SetEqual(PHeapFieldDomain(f.name, h1), PHeapFieldDomain(f.name, h2))
         , Forall( Seq(r)
                 , Implies( SetIn(r, PHeapFieldDomain(f.name, h1))
                          , PHeapLookupField(f.name, fSort, h1, r) === PHeapLookupField(f.name, fSort, h2, r))
                 , Seq( Trigger(Seq(PHeapLookupField(f.name, fSort, h1, r), PHeapLookupField(f.name, fSort, h2, r))))
                 )
      )
    }

    val equalOnPredicates = predicates.foldLeft[Term](True())((ax, p) => And(ax, equalOnPred(p)))
    val equalOnFields = fields.foldLeft[Term](True())((ax, f) => And(ax, equalOnField(f)))

    // TODO: Add scala level PHeapEqual term
    val pheapEqual = App(Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool), Seq(h1,h2))
   
    val frameFunctions = functions.map(g => {
      // TODO: This contains a lot of duplication with the function supporter and relies on its internals.
      // Somehow make it reuse that code.
      val argSorts = g.formalArgs.map(x => symbolConverter.toSort(x.typ))
      val resultSort = symbolConverter.toSort(g.typ)
      val args = g.formalArgs.map(x => Var(Identifier(x.name), symbolConverter.toSort(x.typ)))
      val eqAx = Forall( Seq(h1, h2) ++ args
                      , Implies(pheapEqual, (App(HeapDepFun(Identifier(g.name ++ "%limited"), sorts.PHeap +: argSorts, resultSort), h1 +: args) === App(HeapDepFun(Identifier(g.name ++ "%limited"), sorts.PHeap +: argSorts, resultSort), h2 +: args)))
                      , Seq(Trigger(Seq( App(HeapDepFun(Identifier(g.name ++ "%limited"), sorts.PHeap +: argSorts, resultSort), h1 +: args)
                                       , App(HeapDepFun(Identifier(g.name ++ "%limited"), sorts.PHeap +: argSorts, resultSort), h2 +: args)))))
      eqAx
    })

    val predTriggers = predicates.map(p => {

      val argSorts = p.formalArgs.map(x => symbolConverter.toSort(x.typ))
      val args = p.formalArgs.map(x => Var(Identifier(x.name), symbolConverter.toSort(x.typ)))

      val eqAx = Forall( Seq(h1, h2) ++ args
                      , Implies(pheapEqual, App(Fun(Identifier(p.name ++ "%trigger"), Seq(sorts.PHeap) ++ argSorts, sorts.Bool), h1 +: args) === App(Fun(Identifier(p.name ++ "%trigger"), sorts.PHeap +: argSorts, sorts.Bool), h2 +: args))
                      , Seq(Trigger(Seq(
                    App(Fun(Identifier(p.name ++ "%trigger"), Seq(sorts.PHeap) ++ argSorts, sorts.Bool), h1 +: args) 
                    ,App(Fun(Identifier(p.name ++ "%trigger"), Seq(sorts.PHeap) ++ argSorts, sorts.Bool), h2 +: args) 

                      )),
                      Trigger(Seq(

                    App(Fun(Identifier(p.name ++ "%trigger"), Seq(sorts.PHeap) ++ argSorts, sorts.Bool), h1 +: args) 
                    , pheapEqual
                      ))
                      ))
      eqAx
    })

    val eqSym = Forall( Seq(h1, h2)
                      , pheapEqual === App(Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool), Seq(h2,h1))
                      , Seq(Trigger(pheapEqual))
                      )

    val eqTrans = Forall( Seq(h1, h2, h3)
                        , Implies(And(
                          pheapEqual
                          , App(Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool), Seq(h2,h3))
                        ), App(Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool), Seq(h1,h3))

                        )
                        , Seq(Trigger(Seq(pheapEqual, App(Fun(Identifier("PHeap.equal"), Seq(sorts.PHeap, sorts.PHeap), sorts.Bool), Seq(h2,h3))  )))
                        )

    val extEq = Forall( Seq(h1, h2)
                      , Iff(And(equalOnFields, equalOnPredicates), pheapEqual)
                      , Seq(Trigger(pheapEqual))
                      )

    val eqLift = Forall( Seq(h1, h2)
                       , Implies(h1 === h2, pheapEqual)
                       , Seq(Trigger(pheapEqual))
                       )

    (/*eqSym +:*/ eqLift +: extEq +: frameFunctions) //++ predTriggers
  }

  def predicateSingletonFieldDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_field_domain.smt2"

    predicates flatMap (p => {
      fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"predicate_singleton_field_domain (${p.name}, ${f.name})", declarations)
      })
    })
  }

  def fieldSingletonFieldDomains(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_field_domain.smt2"
    fields flatMap (f2 => {
      fields map (f => {
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

  def fieldSingletonPredicateDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      fields map (f => {
        val declarations = preambleReader.readParametricPreamble(templateFile, fieldSubstitutions(f) ++ predicateSubstitutions(p))
        (s"field_singleton_predicate_domain (${p.name}, ${f.name})", declarations)
      })
    })
  }

  def predicateSingletonPredicateDomains(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      val pred_id = p.name
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val pArgs_q = (p.formalArgs map (a => 
          "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
      )).mkString(" ")
      predicates map (p2 => {
        if (p.name == p.name) {
          ("", Seq())
        } else {
          val substitutions = predicateSubstitutions(p) ++ addKeySuffix(predicateSubstitutions(p2), "2")
          val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
          (s"predicate_singleton_predicate_domain (${p.name}, ${p2.name})", declarations)
        }
      })
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
    astAxioms.map(ax => sink.assume(ax))
    emitPreambleLines(sink, collectedAxioms)
  }

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
