(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(Set_equal
		(PHeap.dom_$FLD$ (PHeap.combine h1 h2))
		(Set_union (PHeap.dom_$FLD$ h1) (PHeap.dom_$FLD$ h2))
	)
	:pattern (PHeap.dom_$FLD$ (PHeap.combine h1 h2))
	:qid |PHeap.field_dom_combine[$FLD$]|)))
