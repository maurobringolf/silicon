// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.state.terms._

trait QuantifierSupporter {
  def autoTrigger(q: Quantification): Quantification

  def detectQuantificationProblems(quantification: Quantification): Seq[String]
}

class DefaultQuantifierSupporter(triggerGenerator: TriggerGenerator) extends QuantifierSupporter {
  def autoTrigger(q: Quantification): Quantification = {
      if (q.triggers.nonEmpty) {
        /* Triggers were given explicitly */
        q
      } else {
        triggerGenerator.generateTriggerSetGroup(q.vars, q.body) match {
          case Some((generatedTriggerSets, extraVariables)) =>
            val generatedTriggers = generatedTriggerSets.map(set => Trigger(set.exps))
            Quantification(q.q, q.vars ++ extraVariables, q.body, generatedTriggers, q.name)
          case _ =>
            q
        }
      }
    }

  def detectQuantificationProblems(quantification: Quantification): Seq[String] = {
    var problems: List[String] = Nil

    quantification.q match {
      case Exists =>
      /* No checks yet */
      case Forall =>
        /* 1. Check that triggers are present */
        if (quantification.triggers.isEmpty)
          problems ::= s"No triggers given"

        /* 2. Check that each trigger set mentions all quantified variables */
        quantification.triggers.foreach(trigger => {
          val vars =
            trigger.p.foldLeft(Set[Var]()){case (varsAcc, term) =>
              varsAcc ++ term.deepCollect{case v: Var => v}}

          if (!quantification.vars.forall(vars.contains))
            problems ::= s"Trigger set $trigger does not contain all quantified variables"
        })

        /* 3. Check that all triggers are valid */
        quantification.triggers.foreach(trigger => trigger.p.foreach{term =>
          if (!triggerGenerator.isPossibleTrigger(term))
            problems ::= s"Trigger $term is not a possible trigger"

          term.deepCollect{case t if triggerGenerator.isForbiddenInTrigger(t) => t}
              .foreach(term => problems ::= s"Term $term may not occur in triggers")
        })
    }

    problems.reverse
  }
}
