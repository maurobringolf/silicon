(declare-fun PHeap.lookup_$MW$ (PHeap Loc) PHeap)
(declare-fun PHeap.dom_$MW$ (PHeap) Set<Loc>)
(declare-fun PHeap.MWloc_$MW$ ($MW_ARGS_S$) Loc)

(declare-fun PHeap.singleton_$MW$ ($MW_ARGS_S$ PHeap) PHeap)

(assert (forall ($MW_ARGS_Q$ (l PHeap)) (!
	(= (PHeap.dom_$MW$ (PHeap.singleton_$MW$ $MW_ARGS$ l)) (Set_singleton $MW_LOC$ ))
	:pattern (PHeap.dom_$MW$ (PHeap.singleton_$MW$ $MW_ARGS$ l))
	:qid |singleton_$MW$_dom_$MW$|)))

(assert (forall ($MW_ARGS_Q$ (l PHeap)) (!
	(= (PHeap.lookup_$MW$ (PHeap.singleton_$MW$ $MW_ARGS$ l) $MW_LOC$) l)
	:pattern (PHeap.lookup_$MW$ (PHeap.singleton_$MW$ $MW_ARGS$ l) $MW_LOC$)
	:qid |singleton_$MW$_lookup_$MW$|)))

(assert (Set_equal
  (PHeap.dom_$MW$ PHeap.emp)
  (as Set_empty Set<Loc>)))
