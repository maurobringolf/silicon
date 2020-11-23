;
; FORK
;

(assert (forall ((@h PHeap) (diz $Ref) (hash Int) (ignoreDeleted Bool) (cap Int)) (!
  (implies
    (and
      (not (= diz $Ref.null))
      (> (Seq_length (PHeap.lookup_Map__keys @h diz)) 0)
      (> (Seq_length (PHeap.lookup_Map__values @h diz)) 0)
      (=
        (Seq_length (PHeap.lookup_Map__keys @h diz))
        (Seq_length (PHeap.lookup_Map__values @h diz)))
      (forall ((i1 Int)) (!
        (implies
          (and (>= i1 0) (< i1 (Seq_length (PHeap.lookup_Map__keys @h diz))))
          (or
            (=
              (PHeap.lookup_Ref__Integer_value @h (Seq_index
                (PHeap.lookup_Map__keys @h diz)
                i1))
              (Map__EMPTY (PHeap.restrict_Map__EMPTY @h )))
            (or
              (=
                (PHeap.lookup_Ref__Integer_value @h (Seq_index
                  (PHeap.lookup_Map__keys @h diz)
                  i1))
                (Map__DELETED (PHeap.restrict_Map__DELETED @h )))
              (>=
                (PHeap.lookup_Ref__Integer_value @h (Seq_index
                  (PHeap.lookup_Map__keys @h diz)
                  i1))
                0))))
        :pattern ((Seq_index (PHeap.lookup_Map__keys @h diz) i1))
        ))
      (and (>= hash 0) (< hash (Seq_length (PHeap.lookup_Map__keys @h diz))))
      (< cap (Seq_length (PHeap.lookup_Map__keys @h diz))))
    (=
      (Map__indexOfLoop @h diz hash ignoreDeleted cap)
      (ite
        (<= cap 0)
        (Map__EMPTY (PHeap.restrict_Map__EMPTY @h ))
        (Map__indexOfLoop%limited (PHeap.restrict_Map__indexOfLoop @h diz (mod (+ hash 1) (Seq_length (PHeap.lookup_Map__keys @h diz))) ignoreDeleted (- cap 1)) diz (mod
          (+ hash 1)
          (Seq_length (PHeap.lookup_Map__keys @h diz))) ignoreDeleted (- cap 1)))))
  :pattern ((Map__indexOfLoop @h diz hash ignoreDeleted cap))
  :qid |definitionalAxiom [Map__indexOfLoop]|)))

; additional restrict axioms for fair comparison (upstream does not have this):

(forall ((@h PHeap) (diz $Ref) (hash Int) (ignoreDeleted Bool) (cap Int)) (!
  (forall ((x@41@00 $Ref)) (!
	(and
	  (iff
		(Set_in x@41@00 (PHeap.dom_Map__keys (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap)))
		(and (= x@41@00 diz) (> $Perm.Write $Perm.No)))
	  (Seq_equal
		(PHeap.lookup_Map__keys (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@41@00)
		(PHeap.lookup_Map__keys @h x@41@00)))
	:pattern ((PHeap.lookup_Map__keys (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@41@00))
	:pattern ((Set_in x@41@00 (PHeap.dom_Map__keys (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))))
	))
  :pattern ((PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))
  :qid |restrictHeapAxiom_dom_Map__keys[Map__indexOfLoop]|))

(forall ((@h PHeap) (diz $Ref) (hash Int) (ignoreDeleted Bool) (cap Int)) (!
  (forall ((x@42@00 $Ref)) (!
	(and
	  (iff
		(Set_in x@42@00 (PHeap.dom_Map__values (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap)))
		(and (= x@42@00 diz) (> $Perm.Write $Perm.No)))
	  (Seq_equal
		(PHeap.lookup_Map__values (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@42@00)
		(PHeap.lookup_Map__values @h x@42@00)))
	:pattern ((PHeap.lookup_Map__values (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@42@00))
	:pattern ((Set_in x@42@00 (PHeap.dom_Map__values (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))))
	))
  :pattern ((PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))
  :qid |restrictHeapAxiom_dom_Map__values[Map__indexOfLoop]|))

  (forall ((@h PHeap) (diz $Ref) (hash Int) (ignoreDeleted Bool) (cap Int)) (!
    (forall ((x@43@00 $Ref)) (!
      (and
        (iff
          (Set_in x@43@00 (PHeap.dom_Ref__Integer_value (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap)))
          (or
            (and
              (and
                (>=
                  (QPinv_Map__indexOfLoop_blom02.vpr@34.13_i2 x@43@00 @h diz hash ignoreDeleted cap)
                  0)
                (<
                  (QPinv_Map__indexOfLoop_blom02.vpr@34.13_i2 x@43@00 @h diz hash ignoreDeleted cap)
                  (Seq_length (PHeap.lookup_Map__keys @h diz))))
              (> $Perm.Write 0))
            (and
              (and
                (>=
                  (QPinv_Map__indexOfLoop_blom02.vpr@35.13_i3 x@43@00 @h diz hash ignoreDeleted cap)
                  0)
                (<
                  (QPinv_Map__indexOfLoop_blom02.vpr@35.13_i3 x@43@00 @h diz hash ignoreDeleted cap)
                  (Seq_length (PHeap.lookup_Map__values @h diz))))
              (> $Perm.Write 0))))
        (=
          (PHeap.lookup_Ref__Integer_value (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@43@00)
          (PHeap.lookup_Ref__Integer_value @h x@43@00)))
      :pattern ((PHeap.lookup_Ref__Integer_value (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap) x@43@00))
      :pattern ((Set_in x@43@00 (PHeap.dom_Ref__Integer_value (PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))))
      ))
    :pattern ((PHeap.restrict_Map__indexOfLoop @h diz hash ignoreDeleted cap))
    :qid |restrictHeapAxiom_dom_Ref__Integer_value[Map__indexOfLoop]|))

;
; UPSTREAM
;

(assert (forall ((s@$ $Snap) (diz@2@00 $Ref) (hash@3@00 Int) (ignoreDeleted@4@00 Bool) (cap@5@00 Int)) (!
  (and
    (forall ((i2@9@00 Int)) (!
      (implies
        (and
          (<
            i2@9@00
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= i2@9@00 0))
        (=
          (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
            i2@9@00))
          i2@9@00))
      :pattern ((Seq_index
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
        i2@9@00))
      ))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
          r))
      :pattern ((inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((i3@12@00 Int)) (!
      (implies
        (and
          (<
            i3@12@00
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= i3@12@00 0))
        (=
          (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
            i3@12@00))
          i3@12@00))
      :pattern ((Seq_index
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
        i3@12@00))
      ))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
          r))
      :pattern ((inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((i2@17@00 Int)) (!
      (implies
        (and
          (<
            i2@17@00
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= i2@17@00 0))
        (=
          (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
            i2@17@00))
          i2@17@00))
      :pattern ((Seq_index
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
        i2@17@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
            (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
          r))
      :pattern ((inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((i3@22@00 Int)) (!
      (implies
        (and
          (<
            i3@22@00
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= i3@22@00 0))
        (=
          (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
            i3@22@00))
          i3@22@00))
      :pattern ((Seq_index
        ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
        i3@22@00))
      :qid |Ref__Integer_value-invOfFct|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          (Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))
            (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
          r))
      :pattern ((inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r))
      :qid |Ref__Integer_value-fctOfInv|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef2|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r))
      :qid |qp.fvfValDef3|))
    (forall ((r $Ref)) (!
      (and
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r) r))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef4|))
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00)))
        (and
          (<
            (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00))))
      :qid |qp.fvfDomDef8|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<
              (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
            (>=
              (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0))
          (and
            (<
              (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
            (>=
              (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0)))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef5|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<
              (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
            (>=
              (inv@18@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0))
          (and
            (<
              (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
            (>=
              (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0)))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r))
      :qid |qp.fvfValDef6|))
    (forall ((r $Ref)) (!
      (and
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r) r))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef7|))
    (forall ((r $Ref)) (!
      (iff
        (Set_in r ($FVF.domain_Ref__Integer_value (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00)))
        (and
          (<
            (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0)))
      :pattern ((Set_in r ($FVF.domain_Ref__Integer_value (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00))))
      :qid |qp.fvfDomDef13|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (and
            (<
              (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
            (>=
              (inv@23@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0))
          (and
            (<
              (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              (Seq_length
                ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
            (>=
              (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
              0)))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef11|))
    (forall ((r $Ref)) (!
      ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
      :pattern (($FVF.lookup_Ref__Integer_value (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef12|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@28@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@28@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef14|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@28@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@28@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r))
      :qid |qp.fvfValDef15|))
    (forall ((r $Ref)) (!
      (and
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r) r))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@28@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef16|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@30@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@30@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef19|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@30@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@30@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r))
      :qid |qp.fvfValDef20|))
    (forall ((r $Ref)) (!
      (and
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r) r))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@30@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef21|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
          (>= (inv@13@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@32@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@32@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r))
      :qid |qp.fvfValDef24|))
    (forall ((r $Ref)) (!
      (implies
        (and
          (<
            (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))))
          (>= (inv@10@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00 r) 0))
        (=
          ($FVF.lookup_Ref__Integer_value (sm@32@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r)
          ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r)))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@32@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :pattern (($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r))
      :qid |qp.fvfValDef25|))
    (forall ((r $Ref)) (!
      (and
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$))))))))) r) r)
        ($FVF.loc_Ref__Integer_value ($FVF.lookup_Ref__Integer_value ($SortWrappers.$SnapTo$FVF<Int> ($Snap.first ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second ($Snap.second s@$)))))))) r) r))
      :pattern (($FVF.lookup_Ref__Integer_value (sm@32@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) r))
      :qid |qp.fvfResTrgDef26|))
    (implies
      (and
        (not (= diz@2@00 $Ref.null))
        (>
          (Seq_length
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))
          0)
        (>
          (Seq_length
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$)))))
          0)
        (=
          (Seq_length
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))
          (Seq_length
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second ($Snap.second s@$))))))
        (forall ((i1 Int)) (!
          (implies
            (and
              (>= i1 0)
              (<
                i1
                (Seq_length
                  ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))))
            (or
              (=
                ($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) (Seq_index
                  ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
                  i1))
                (Map__EMPTY $Snap.unit))
              (or
                (=
                  ($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) (Seq_index
                    ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
                    i1))
                  (Map__DELETED $Snap.unit))
                (>=
                  ($FVF.lookup_Ref__Integer_value (sm@14@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00) (Seq_index
                    ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
                    i1))
                  0))))
          :pattern ((Seq_index
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$)))
            i1))
          ))
        (and
          (>= hash@3@00 0)
          (<
            hash@3@00
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))))
        (<
          cap@5@00
          (Seq_length
            ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))))
      (=
        (Map__indexOfLoop s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00)
        (ite
          (<= cap@5@00 0)
          (Map__EMPTY $Snap.unit)
          (Map__indexOfLoop%limited ($Snap.combine
            $Snap.unit
            ($Snap.combine
              ($Snap.first ($Snap.second s@$))
              ($Snap.combine
                ($Snap.first ($Snap.second ($Snap.second s@$)))
                ($Snap.combine
                  $Snap.unit
                  ($Snap.combine
                    $Snap.unit
                    ($Snap.combine
                      $Snap.unit
                      ($Snap.combine
                        ($SortWrappers.$FVF<Int>To$Snap (sm@21@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00))
                        ($Snap.combine
                          ($SortWrappers.$FVF<Int>To$Snap (sm@26@00 s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00))
                          ($Snap.combine
                            $Snap.unit
                            ($Snap.combine
                              $Snap.unit
                              ($Snap.combine $Snap.unit $Snap.unit))))))))))) diz@2@00 (mod
            (+ hash@3@00 1)
            (Seq_length
              ($SortWrappers.$SnapToSeq<$Ref> ($Snap.first ($Snap.second s@$))))) ignoreDeleted@4@00 (-
            cap@5@00
            1))))))
  :pattern ((Map__indexOfLoop s@$ diz@2@00 hash@3@00 ignoreDeleted@4@00 cap@5@00))
  )))
