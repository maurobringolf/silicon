(declare-fun PHeap.lookup_$PRD$ (PHeap Loc) PHeap)
(declare-fun PHeap.dom_$PRD$ (PHeap) Set<Loc>)
(declare-fun PHeap.loc_$PRD$ ($PRD_ARGS_S$) Loc)

(declare-fun PHeap.singleton_$PRD$ ($PRD_ARGS_S$ PHeap) PHeap)
(declare-fun PHeap.remove_$PRD$ (PHeap $PRD_ARGS_S$) PHeap)

(declare-fun PHeap.funTrigger_$PRD$ (PHeap) PHeap)

(assert (forall ((h PHeap)) (!
	(= (PHeap.funTrigger_$PRD$ h) h)
	:pattern ((PHeap.funTrigger_$PRD$ h)))))

(assert (forall ((h1 PHeap) $PRD_ARGS_Q$ (h2 PHeap)) (!
  (implies
    ;(and
		(PHeap.equal (PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$)) h2)
		;($PRD$%trigger h2 $PRD_ARGS$)
	;)
    ($PRD$%trigger (PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$)) $PRD_ARGS$)
  )
  :pattern ((PHeap.funTrigger_$PRD$ h1) ($PRD$%trigger h2 $PRD_ARGS$)))))

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
