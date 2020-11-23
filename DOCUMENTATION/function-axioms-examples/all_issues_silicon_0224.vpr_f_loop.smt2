;
; FORK
;

(assert (forall ((@h PHeap) (a IArray) (x Int) (y Int) (n Int)) (!
(implies
(and
  (and
	(and (<= 0 x) (< x (length<Int> a)))
	(and (<= 0 y) (< y (length<Int> a))))
  (and
	(<= 0 n)
	(and (<= (+ x n) (length<Int> a)) (<= (+ y n) (length<Int> a)))))
(=
  (f_loop @h a x y n)
  (ite
	(and
	  (< (+ x n) (length<Int> a))
	  (and
		(< (+ y n) (length<Int> a))
		(=
		  (PHeap.lookup_val @h (loc<Ref> a (+ x n)))
		  (PHeap.lookup_val @h (loc<Ref> a (+ y n))))))
	(f_loop%limited (PHeap.restrict_f_loop @h a x y (+ n 1)) a x y (+ n 1))
	n)))
:pattern ((f_loop @h a x y n))
:qid |definitionalAxiom [f_loop]|)))

; additional restrict axioms for fair comparison (upstream does not have this):

(assert (forall ((@h PHeap) (a IArray) (x Int) (y Int) (n Int)) (!
  (forall ((x@38@00 $Ref)) (!
    (and
      (iff
        (Set_in x@38@00 (PHeap.dom_val (PHeap.restrict_f_loop @h a x y n)))
        (and
          (and
            (<= 0 (QPinv_f_loop_0224.vpr@50.9_k x@38@00 @h a x y n))
            (< (QPinv_f_loop_0224.vpr@50.9_k x@38@00 @h a x y n) (length<Int> a)))
          (> $Perm.Write 0)))
      (=
        (PHeap.lookup_val (PHeap.restrict_f_loop @h a x y n) x@38@00)
        (PHeap.lookup_val @h x@38@00)))
    :pattern ((PHeap.lookup_val (PHeap.restrict_f_loop @h a x y n) x@38@00))
    :pattern ((Set_in x@38@00 (PHeap.dom_val (PHeap.restrict_f_loop @h a x y n))))
    ))
  :pattern ((PHeap.restrict_f_loop @h a x y n))
  :qid |restrictHeapAxiom_dom_val[f_loop]|)))

;
; UPSTREAM
;

(assert (forall ((s@$ $Snap) (a@0@00 IArray) (x@1@00 Int) (y@2@00 Int) (n@3@00 Int)) (!
  (and
    (forall ((k@11@00 Int)) (!
      (implies
        (and (< k@11@00 (length<Int> a@0@00)) (<= 0 k@11@00))
        (=
          (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 (loc<Ref> a@0@00 k@11@00))
          k@11@00))
      :pattern ((loc<Ref> a@0@00 k@11@00))
      ))
    (forall ((r $Ref)) (!
      (implies
        (and
          (< (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r) (length<Int> a@0@00))
          (<= 0 (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)))
        (= (loc<Ref> a@0@00 (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)) r))
      :pattern ((inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r))
      :qid |val-fctOfInv|))
    (forall ((k@15@00 Int)) (!
      (implies
        (and (< k@15@00 (length<Int> a@0@00)) (<= 0 k@15@00))
        (=
          (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 (loc<Ref> a@0@00 k@15@00))
          k@15@00))
      :pattern ((loc<Ref> a@0@00 k@15@00))
      :qid |val-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (< (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r) (length<Int> a@0@00))
          (<= 0 (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)))
        (= (loc<Ref> a@0@00 (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)) r))
      :pattern ((inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r))
      :qid |val-fctOfInv|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (< (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r) (length<Int> a@0@00))
          (<= 0 (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)))
        (=
          ($FVF.lookup_val (sm@13@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r)
          ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r)))
      :pattern (($FVF.lookup_val (sm@13@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r))
      :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r))
      :qid |qp.fvfValDef0|))
    (forall ((r $Ref)) (!
      ($FVF.loc_val ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r) r)
      :pattern (($FVF.lookup_val (sm@13@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r))
      :qid |qp.fvfResTrgDef1|))
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_val (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00)))
        (and
          (< (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r) (length<Int> a@0@00))
          (<= 0 (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r))))
      :pattern ((Set_in r ($FVF.domain_val (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00))))
      :qid |qp.fvfDomDef4|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<
              (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)
              (length<Int> a@0@00))
            (<= 0 (inv@16@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)))
          (and
            (<
              (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r)
              (length<Int> a@0@00))
            (<= 0 (inv@12@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00 r))))
        (=
          ($FVF.lookup_val (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r)
          ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r)))
      :pattern (($FVF.lookup_val (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r))
      :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r))
      :qid |qp.fvfValDef2|))
    (forall ((r $Ref)) (!
      ($FVF.loc_val ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first s@$)) r) r)
      :pattern (($FVF.lookup_val (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) r))
      :qid |qp.fvfResTrgDef3|))
    (implies
      (and
        (and
          (and (<= 0 x@1@00) (< x@1@00 (length<Int> a@0@00)))
          (and (<= 0 y@2@00) (< y@2@00 (length<Int> a@0@00))))
        (and
          (<= 0 n@3@00)
          (and
            (<= (+ x@1@00 n@3@00) (length<Int> a@0@00))
            (<= (+ y@2@00 n@3@00) (length<Int> a@0@00)))))
      (=
        (f_loop s@$ a@0@00 x@1@00 y@2@00 n@3@00)
        (ite
          (and
            (< (+ x@1@00 n@3@00) (length<Int> a@0@00))
            (and
              (< (+ y@2@00 n@3@00) (length<Int> a@0@00))
              (=
                ($FVF.lookup_val (sm@13@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) (loc<Ref> a@0@00 (+
                  x@1@00
                  n@3@00)))
                ($FVF.lookup_val (sm@13@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00) (loc<Ref> a@0@00 (+
                  y@2@00
                  n@3@00))))))
          (f_loop%limited ($Snap.combine
            ($SortWrappers.$FVF<Int>To$Snap (sm@18@00 s@$ a@0@00 x@1@00 y@2@00 n@3@00))
            ($Snap.combine
              $Snap.unit
              ($Snap.combine
                $Snap.unit
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine $Snap.unit $Snap.unit))))))) a@0@00 x@1@00 y@2@00 (+
            n@3@00
            1))
          n@3@00))))
  :pattern ((f_loop s@$ a@0@00 x@1@00 y@2@00 n@3@00))
  )))
