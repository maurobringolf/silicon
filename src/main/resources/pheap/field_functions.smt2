(declare-fun PHeap.lookup_$FLD$ (PHeap $Ref) $S$)
(declare-fun PHeap.dom_$FLD$ (PHeap) Set<$Ref>)

(declare-fun PHeap.singleton_$FLD$ ($Ref $S$) PHeap)
(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$FLD$ (PHeap.singleton_$FLD$ x v)) (Set_singleton x))
	:pattern (PHeap.dom_$FLD$ (PHeap.singleton_$FLD$ x v))
	:qid |singleton_$FLD$_dom_$FLD$|)))

(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.lookup_$FLD$ (PHeap.singleton_$FLD$ x v) x) v)
	:pattern (PHeap.lookup_$FLD$ (PHeap.singleton_$FLD$ x v) x)
	:qid |singleton_$FLD$_lookup_$FLD$|)))

(assert (Set_equal
	(PHeap.dom_$FLD$ PHeap.emp)
	(as Set_empty Set<$Ref>)))

; TODO: Move all embedding related things to a separate file
(declare-fun $FVF.toPHeap_$FLD$ ($FVF<$S$>) PHeap)
(declare-fun PHeap.toFVF_$FLD$ (PHeap) $FVF<$S$>)

(assert (forall ((h PHeap) (x $Ref)) (!
    (implies
        (Set_in x (PHeap.dom_$FLD$ h))
        (=
            (PHeap.lookup_$FLD$ h x)
            ($FVF.lookup_$FLD$ (PHeap.toFVF_$FLD$ h) x)
        )
    )
    :pattern (($FVF.lookup_$FLD$ (PHeap.toFVF_$FLD$ h) x))
    :pattern ((PHeap.lookup_$FLD$ h x) (PHeap.toFVF_$FLD$ h))
    :pattern ((Set_in x (PHeap.dom_$FLD$ h)) (PHeap.toFVF_$FLD$ h))
    )))

(assert (forall ((h PHeap)) (!
    (=
        ($FVF.domain_$FLD$ (PHeap.toFVF_$FLD$ h))
        (PHeap.dom_$FLD$ h))
    :pattern (($FVF.domain_$FLD$ (PHeap.toFVF_$FLD$ h)))
    :pattern ((PHeap.toFVF_$FLD$ h))
    :pattern ((PHeap.dom_$FLD$ h) (PHeap.toFVF_$FLD$ h))
    )))

(assert (forall ((fvf $FVF<$S$>) (x $Ref)) (!
    (implies
        (Set_in x ($FVF.domain_$FLD$ fvf))
        (=
            ($FVF.lookup_$FLD$ fvf x)
            (PHeap.lookup_$FLD$ ($FVF.toPHeap_$FLD$ fvf) x)
        )
    )
    :pattern ((Set_in x (PHeap.dom_$FLD$ ($FVF.toPHeap_$FLD$ fvf))))
    :pattern ((PHeap.lookup_$FLD$ ($FVF.toPHeap_$FLD$ fvf) x))
    :pattern ((Set_in x ($FVF.domain_$FLD$ fvf)) 
    ))))

(assert (forall ((fvf $FVF<$S$>) (x $Ref)) (!
    (=
        (Set_in x ($FVF.domain_$FLD$ fvf))
        (Set_in x (PHeap.dom_$FLD$ ($FVF.toPHeap_$FLD$ fvf)))
    )
    :pattern ((Set_in x (PHeap.dom_$FLD$ ($FVF.toPHeap_$FLD$ fvf))))
    :pattern ((Set_in x ($FVF.domain_$FLD$ fvf)))
    )))

