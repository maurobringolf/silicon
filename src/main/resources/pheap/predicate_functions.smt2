(declare-fun PHeap.lookup_$PRD$ (PHeap Loc) PHeap)
(declare-fun PHeap.dom_$PRD$ (PHeap) Set<Loc>)
(declare-fun PHeap.loc_$PRD$ ($PRD_ARGS_S$) Loc)

(declare-fun PHeap.singleton_$PRD$ ($PRD_ARGS_S$ PHeap) PHeap)
(declare-fun PHeap.remove_$PRD$ (PHeap $PRD_ARGS_S$) PHeap)

(define-fun PHeap.unfold_$PRD$ ((h PHeap) $PRD_ARGS_Q$ (rc Bool)) PHeap
	(PHeap.combine
		(PHeap.lookup_$PRD$ h $PRD_LOC$)
		(ite rc (PHeap.remove_$PRD$ h $PRD_ARGS$) h)
	))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(=
		(PHeap.dom_$PRD$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
		(Set_difference
			(PHeap.dom_$PRD$ h)
			(Set_singleton $PRD_LOC$)
		)
	)
	:pattern (PHeap.dom_$PRD$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
	:qid |dom_$PRD$_remove_$PRD$|)))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (Set_singleton $PRD_LOC$ ))
	:pattern (PHeap.dom_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h))
	:qid |singleton_$PRD$_dom_$PRD$|)))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.lookup_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h) $PRD_LOC$) h)
	:pattern (PHeap.lookup_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h) $PRD_LOC$)
	:qid |singleton_$PRD$_lookup_$PRD$|)))

(assert (Set_equal
  (PHeap.dom_$PRD$ PHeap.emp)
  (as Set_empty Set<Loc>)))
