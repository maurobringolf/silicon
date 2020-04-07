(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$PRD$ (PHeap.singleton_$FLD$ x v)) (as Set_empty Set<Loc>))
	:pattern (PHeap.dom_$PRD$ (PHeap.singleton_$FLD$ x v))
	:qid |singleton_$FLD$_dom_$PRD$|)))

(assert (forall ((fvf $FVF<$S$>) (l Loc)) (!
	(not (Set_in l (PHeap.dom_$PRD$ ($FVF.toPHeap_$FLD$ fvf))))
    :pattern ((Set_in l (PHeap.dom_$PRD$ ($FVF.toPHeap_$FLD$ fvf))))
    )))