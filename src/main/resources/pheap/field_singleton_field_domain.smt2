(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$FLD2$ (PHeap.singleton_$FLD$ x v)) (as Set_empty Set<$Ref>))
	:pattern (PHeap.dom_$FLD2$ (PHeap.singleton_$FLD$ x v))
	:qid |singleton_$FLD$_dom_$FLD2$|)))

(assert (forall ((fvf $FVF<$S$>) (x $Ref)) (!
	(not (Set_in x (PHeap.dom_$FLD2$ ($FVF.toPHeap_$FLD$ fvf))))
    :pattern ((Set_in x (PHeap.dom_$FLD2$ ($FVF.toPHeap_$FLD$ fvf))))
    )))