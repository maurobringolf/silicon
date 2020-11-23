;
; FORK
;

(assert (forall ((@h PHeap) (hdrs $Ref) (index Int)) (!
  (implies
    (and (>= index 0) (<= index (Seq_length (PHeap.lookup_list_acc @h hdrs))))
    (=
      (extension_len_rec @h hdrs index)
      (let ((cond_0 (= index (Seq_length (PHeap.lookup_list_acc @h hdrs))))) (ite
        cond_0
        0
        (extension_len_rec%limited (PHeap.restrict_extension_len_rec @h hdrs (+ index 1)) hdrs (+
          index
          1))))))
  :pattern ((extension_len_rec @h hdrs index))
  :qid |definitionalAxiom [extension_len_rec]|)))

; additional restrict axioms for fair comparison (upstream does not have this):

(forall ((@h PHeap) (hdrs $Ref) (index Int)) (!
    (forall ((x@15@00 $Ref)) (!
      (and
        (iff
          (Set_in x@15@00 (PHeap.dom_list_acc (PHeap.restrict_extension_len_rec @h hdrs index)))
          (and (= x@15@00 hdrs) (> (/ (to_real 1) (to_real 200)) $Perm.No)))
        (Seq_equal
          (PHeap.lookup_list_acc (PHeap.restrict_extension_len_rec @h hdrs index) x@15@00)
          (PHeap.lookup_list_acc @h x@15@00)))
      :pattern ((PHeap.lookup_list_acc (PHeap.restrict_extension_len_rec @h hdrs index) x@15@00))
      :pattern ((Set_in x@15@00 (PHeap.dom_list_acc (PHeap.restrict_extension_len_rec @h hdrs index))))
      ))
    :pattern ((PHeap.restrict_extension_len_rec @h hdrs index))
    :qid |restrictHeapAxiom_dom_list_acc[extension_len_rec]|))

(forall ((@h PHeap) (hdrs $Ref) (index Int)) (!
    (forall ((loc@17@00 Loc)) (!
      (and
        (iff
          (Set_in loc@17@00 (PHeap.dom_asdasd (PHeap.restrict_extension_len_rec @h hdrs index)))
          (and
            (Seq_contains
              (PHeap.lookup_list_acc @h hdrs)
              (QPinv_extension_len_rec_0192.vpr@10.13_lambda180_26$e loc@17@00 @h hdrs index))
            (> (/ (to_real 1) (to_real 200)) 0)))
        (implies
          (Set_in loc@17@00 (PHeap.dom_asdasd (PHeap.restrict_extension_len_rec @h hdrs index)))
          (=
            (PHeap.lookup_asdasd (PHeap.restrict_extension_len_rec @h hdrs index) loc@17@00)
            (PHeap.lookup_asdasd @h loc@17@00))))
      :pattern ((Set_in loc@17@00 (PHeap.dom_asdasd (PHeap.restrict_extension_len_rec @h hdrs index))))
      :pattern ((PHeap.lookup_asdasd (PHeap.restrict_extension_len_rec @h hdrs index) loc@17@00))
      ))
    :pattern ((PHeap.restrict_extension_len_rec @h hdrs index))
    :qid |restrictHeapAxiom_dom_asdasd[extension_len_rec]|))

;
; UPSTREAM
;

(assert (forall ((s@$ $Snap) (hdrs@0@00 $Ref) (index@1@00 Int)) (!
  (and
    (forall ((lambda180_26$e@3@00 $Ref)) (!
      (implies
        (Seq_contains
          ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
          lambda180_26$e@3@00)
        (=
          (inv@4@00 s@$ hdrs@0@00 index@1@00 lambda180_26$e@3@00)
          lambda180_26$e@3@00))
      :pattern ((Seq_contains
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
        lambda180_26$e@3@00))
      :pattern ((inv@4@00 s@$ hdrs@0@00 index@1@00 lambda180_26$e@3@00))
      ))
    (forall ((r $Ref)) (!
      (implies
        (Seq_contains
          ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
          (inv@4@00 s@$ hdrs@0@00 index@1@00 r))
        (= (inv@4@00 s@$ hdrs@0@00 index@1@00 r) r))
      :pattern ((inv@4@00 s@$ hdrs@0@00 index@1@00 r))
      :qid |asdasd-fctOfInv|))
    (forall ((lambda180_26$e@7@00 $Ref)) (!
      (implies
        (Seq_contains
          ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
          lambda180_26$e@7@00)
        (=
          (inv@8@00 s@$ hdrs@0@00 index@1@00 lambda180_26$e@7@00)
          lambda180_26$e@7@00))
      :pattern ((Seq_contains
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
        lambda180_26$e@7@00))
      :pattern ((inv@8@00 s@$ hdrs@0@00 index@1@00 lambda180_26$e@7@00))
      :qid |asdasd-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (Seq_contains
          ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
          (inv@8@00 s@$ hdrs@0@00 index@1@00 r))
        (= (inv@8@00 s@$ hdrs@0@00 index@1@00 r) r))
      :pattern ((inv@8@00 s@$ hdrs@0@00 index@1@00 r))
      :qid |asdasd-fctOfInv|))
    (forall ((s@11@00 $Snap)) (!
      (iff
        (Set_in s@11@00 ($PSF.domain_asdasd (sm@10@00 s@$ hdrs@0@00 index@1@00)))
        (Seq_contains
          ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
          (inv@8@00 s@$ hdrs@0@00 index@1@00 ($SortWrappers.$SnapTo$Ref s@11@00))))
      :pattern ((Set_in s@11@00 ($PSF.domain_asdasd (sm@10@00 s@$ hdrs@0@00 index@1@00))))
      :qid |qp.psmDomDef4|))
    (forall ((s@11@00 $Snap)) (!
      (implies
        (and
          (Seq_contains
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
            (inv@8@00 s@$ hdrs@0@00 index@1@00 ($SortWrappers.$SnapTo$Ref s@11@00)))
          (Seq_contains
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$))
            (inv@4@00 s@$ hdrs@0@00 index@1@00 ($SortWrappers.$SnapTo$Ref s@11@00))))
        (and
          (not (= s@11@00 $Snap.unit))
          (=
            ($PSF.lookup_asdasd (sm@10@00 s@$ hdrs@0@00 index@1@00) s@11@00)
            ($PSF.lookup_asdasd ($SortWrappers.$SnapTo$PSF<$Snap> ($Snap.first ($Snap.second s@$))) s@11@00))))
      :pattern (($PSF.lookup_asdasd (sm@10@00 s@$ hdrs@0@00 index@1@00) s@11@00))
      :pattern (($PSF.lookup_asdasd ($SortWrappers.$SnapTo$PSF<$Snap> ($Snap.first ($Snap.second s@$))) s@11@00))
      :qid |qp.psmValDef2|))
    (forall ((s@11@00 $Snap)) (!
      ($PSF.loc_asdasd ($PSF.lookup_asdasd ($SortWrappers.$SnapTo$PSF<$Snap> ($Snap.first ($Snap.second s@$))) s@11@00) s@11@00)
      :pattern (($PSF.lookup_asdasd (sm@10@00 s@$ hdrs@0@00 index@1@00) s@11@00))
      :qid |qp.psmResTrgDef3|))
    (implies
      (and
        (>= index@1@00 0)
        (<=
          index@1@00
          (Seq_length ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$)))))
      (=
        (extension_len_rec s@$ hdrs@0@00 index@1@00)
        (let ((cond_0 (=
          index@1@00
          (Seq_length ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first s@$)))))) (ite
          cond_0
          0
          (extension_len_rec%limited ($Snap.combine
            ($Snap.first s@$)
            ($Snap.combine
              ($SortWrappers.$PSF<$Snap>To$Snap (sm@10@00 s@$ hdrs@0@00 index@1@00))
              ($Snap.combine $Snap.unit $Snap.unit))) hdrs@0@00 (+ index@1@00 1)))))))
  :pattern ((extension_len_rec s@$ hdrs@0@00 index@1@00))
  )))
