; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $PRD$ is a Silver predicate name

; ATTENTION: The triggers mention the sort wrappers introduced for PSFs.
; The axiom therefore needs to be emitted after the sort wrappers have
; been emitted.

(assert (forall ((l Loc) (pm $PPM)) (!
    ($Perm.isValidVar ($PSF.perm_$PRD$ pm l))
    :pattern ($PSF.perm_$PRD$ pm l))))

(assert (forall ((l Loc) (h PHeap)) (!
    (= ($PSF.loc_$PRD$ l h) true)
    :pattern ($PSF.loc_$PRD$ l h))))
