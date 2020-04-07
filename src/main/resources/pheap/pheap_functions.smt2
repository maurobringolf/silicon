(declare-fun PHeap.combine (PHeap PHeap) PHeap)
(declare-fun PHeap.equal (PHeap PHeap) Bool)
(declare-const PHeap.emp PHeap)

; TODO: (re)move this
(declare-fun freshWildcard (Int) $Perm)

(assert (forall ((i Int)) (!
    (> (freshWildcard i) 0)
    :pattern ((freshWildcard i)))))
