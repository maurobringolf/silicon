(declare-fun PHeap.combine (PHeap PHeap) PHeap)
(declare-fun PHeap.equal (PHeap PHeap) Bool)
(declare-fun PHeap.subheap (PHeap PHeap) Bool)
(declare-const PHeap.emp PHeap)

(declare-fun PHeap.MWS (PHeap PHeap) PHeap)
(declare-fun PHeap.LHS (PHeap) PHeap)
(declare-fun PHeap.RHS (PHeap) PHeap)

(assert (forall ((h1 PHeap) (h2 PHeap)) (!
    (= (PHeap.LHS (PHeap.MWS h1 h2)) h1)
    :pattern (PHeap.LHS (PHeap.MWS h1 h2)))))

(assert (forall ((h1 PHeap) (h2 PHeap)) (!
    (= (PHeap.RHS (PHeap.MWS h1 h2)) h2)
    :pattern (PHeap.RHS (PHeap.MWS h1 h2)))))

(assert (forall ((h PHeap)) (!
    (= h (PHeap.MWS (PHeap.LHS h) (PHeap.RHS h)))
    :pattern ((PHeap.MWS (PHeap.LHS h) (PHeap.RHS h))))))
