/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silicon.interfaces.state.{Chunk, PermissionChunk}
import viper.silicon.resources.{FieldID, PredicateID, ResourceID}
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state.terms._
import viper.silver.ast

case class BasicChunk(resourceID: ResourceID,
                      name: String,
                      args: Seq[Term],
                      snap: Term,
                      perm: Term)
  extends PermissionChunk {

  // TODO: needed?
  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")
  resourceID match {
    case FieldID() => assert(snap.sort != sorts.Snap, s"A field chunk's value ($snap) is not expected to be of sort Snap")
    case PredicateID() => assert(snap.sort == sorts.Snap,
      s"A predicate chunk's snapshot ($snap) is expected to be of sort Snap, but found ${snap.sort}")
  }

  def duplicate(resourceID: ResourceID = resourceID, name: String = name, args: Seq[Term] = args, snap: Term = snap,
                perm: Term = perm): BasicChunk = BasicChunk(resourceID, name, args, snap, perm)

  def +(perm: Term): BasicChunk = duplicate(perm = PermPlus(this.perm, perm))
  def -(perm: Term): BasicChunk = duplicate(perm = PermMinus(this.perm, perm))
  def \(perm: Term): BasicChunk = duplicate(perm = perm)

  override def toString = resourceID match {
    case FieldID() =>
      val rcvr = args.head
      s"$rcvr.$name -> $snap # $perm"
    case PredicateID() => s"$name($snap; ${args.mkString(",")}) # $perm"
  }

}

sealed trait QuantifiedChunk extends PermissionChunk {
  type Self <: QuantifiedChunk

  def name: String
  def snapshotMap: Term
  def singletonArguments: Option[Seq[Term]]
  def hints: Seq[Term]

  def valueAt(arguments: Seq[Term]): Term

  def duplicate(name: String = name,
                snapshotMap: Term = snapshotMap,
                perm: Term,
                singletonArguments: Option[Seq[Term]] = singletonArguments,
                hints: Seq[Term] = hints)
               : Self
}


/* TODO: Instead of using the singletonRcvr to differentiate between QP chunks that
 *       provide permissions to a single location and those providing permissions
 *       to potentially multiple locations, consider using regular, non-quantified
 *       chunks instead.
 */
case class QuantifiedFieldChunk(name: String,
                                fvf: Term,
                                perm: Term,
                                invs: Option[InverseFunctions],
                                initialCond: Option[Term],
                                singletonRcvr: Option[Term],
                                hints: Seq[Term] = Nil)
    extends QuantifiedChunk {

  assert(fvf.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         s"Quantified chunk values must be of sort FieldValueFunction, but found value $fvf of sort ${fvf.sort}")

  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  type Self = QuantifiedFieldChunk

  def snapshotMap: Term = fvf
  def singletonArguments: Option[Seq[Term]] = singletonRcvr.map(Seq(_))

  def valueAt(rcvr: Term): Term = Lookup(name, fvf, rcvr)

  def valueAt(arguments: Seq[Term]): Term = {
    assert(arguments.length == 1)

    Lookup(name, fvf, arguments.head)
  }

  def +(perm: Term): QuantifiedFieldChunk = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): QuantifiedFieldChunk = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term): QuantifiedFieldChunk = copy(perm = perm)

  override def toString = s"${terms.Forall} ${`?r`} :: ${`?r`}.$name -> $fvf # $perm"

  def duplicate(name: String,
                snapshotMap: Term,
                perm: Term,
                singletonArguments: Option[Seq[Term]],
                hints: Seq[Term])
               : Self = {

    copy(name, fvf, perm, invs, initialCond, singletonRcvr, hints)
  }
}

case class QuantifiedPredicateChunk(name: String,
                                    formalVars: Seq[Var],
                                    psf: Term,
                                    perm: Term,
                                    invs: Option[InverseFunctions],
                                    initialCond: Option[Term],
                                    singletonArgs: Option[Seq[Term]],
                                    hints: Seq[Term] = Nil)
    extends QuantifiedChunk {

  assert(psf.sort.isInstanceOf[terms.sorts.PredicateSnapFunction], s"Quantified predicate chunk values must be of sort PredicateSnapFunction ($psf), but found ${psf.sort}")
  assert(perm.sort == sorts.Perm, s"Permissions $perm must be of sort Perm, but found ${perm.sort}")

  type Self = QuantifiedPredicateChunk

  def snapshotMap: Term = psf
  def singletonArguments: Option[Seq[Term]] = singletonArgs

  def valueAt(args: Seq[Term]) = PredicateLookup(name, psf, args)

  def +(perm: Term): QuantifiedPredicateChunk = copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): QuantifiedPredicateChunk = copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term): QuantifiedPredicateChunk = copy(perm = perm)

  override def toString = s"${terms.Forall}  ${formalVars.mkString(",")} :: $name(${formalVars.mkString(",")}) -> $psf # $perm"

  def duplicate(name: String,
                snapshotMap: Term,
                perm: Term,
                singletonArguments: Option[Seq[Term]],
                hints: Seq[Term])
               : Self = {

    copy(name, formalVars, psf, perm, invs, initialCond, singletonArgs, hints)
  }
}

case class MagicWandChunk(ghostFreeWand: ast.MagicWand,
                          bindings: Map[ast.AbstractLocalVar, Term],
                          evaluatedTerms: Seq[Term])
    extends Chunk {

  override lazy val toString: String = {
    val pos = ghostFreeWand.pos match {
      case rp: viper.silver.ast.HasLineColumn => s"${rp.line}:${rp.column}"
      case other => other.toString
    }

    s"wand@$pos[${evaluatedTerms.mkString(",")}]"
  }
}
