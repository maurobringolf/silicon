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

(assert (forall ((h1 PHeap) (h2 PHeap) $MW_ARGS_Q$)
	(!
		(=>
			(Set_in $MW_LOC$ (PHeap.dom_$MW$ h1))
			(=
				(PHeap.lookup_$MW$ (PHeap.combine h1 h2) $MW_LOC$)
				(PHeap.lookup_$MW$ h1 $MW_LOC$)
			)
		)
		:pattern (PHeap.lookup_$MW$ (PHeap.combine h1 h2) $MW_LOC$)
		:pattern ((PHeap.lookup_$MW$ h1 $MW_LOC$) (PHeap.combine h1 h2))
		:qid |PHeap.mw_lookup_combine[$MW$]|)))



