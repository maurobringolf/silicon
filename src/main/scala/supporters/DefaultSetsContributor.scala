// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import scala.reflect.{ClassTag, classTag}
import viper.silicon.Config
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{Sort, Term, sorts}

class DefaultSetsContributor(val domainTranslator: DomainsTranslator[Term], config: Config)
    extends BuiltinDomainsContributor {

  type BuiltinDomainType = ast.SetType
  val builtinDomainTypeTag: ClassTag[BuiltinDomainType] = classTag[ast.SetType]

  val defaultSourceResource: String = "/dafny_axioms/sets.vpr"
  val userProvidedSourceFilepath: Option[String] = config.setAxiomatizationFile.toOption
  val sourceDomainName: String = "$Set"

  override def computeGroundTypeInstances(program: ast.Program): InsertionOrderedSet[ast.SetType] = {
    var setTypeInstances = super.computeGroundTypeInstances(program)

    /* 
     * PHeap snapshots depend on Set<$Ref> for domains, just like quantified permission snapshot maps
     *
     * TODO: It shouldn't be the responsibility of the sets contributor to add set types required by QPs and PHeaps
     */
    setTypeInstances += ast.SetType(ast.Ref)
    setTypeInstances += ast.SetType((new ast.DomainType("Loc", Map.empty[ast.TypeVar, ast.Type])(Seq())))

    setTypeInstances
  }

  def targetSortFactory(argumentSorts: Iterable[Sort]): Sort = {
    assert(argumentSorts.size == 1)
    sorts.Set(argumentSorts.head)
  }
}

