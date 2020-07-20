(assert (forall ($MW_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$FLD$ (PHeap.singleton_$MW$ $MW_ARGS$ h)) (as Set_empty Set<$Ref>))
	:pattern (PHeap.dom_$FLD$ (PHeap.singleton_$MW$ $MW_ARGS$ h))
	:qid |singleton_$MW$_dom_$FLD$|)))

