(declare-sort Room)
(declare-const lob Room)
(declare-const bur Room)
(declare-const mr Room)
(declare-const cor Room)
(declare-const out Room)
(assert (distinct lob bur mr cor out))
(assert (forall ((r Room)) (or (= r lob) (= r bur) (= r mr) (= r cor) (= r out))))
(declare-const lob_cor_hole0 Int)
(declare-const lob_cor_hole1 Int)
(declare-const lob_cor_hole2 Int)
(declare-const lob_cor_hole3 Int)
(declare-const lob_out_hole0 Int)
(declare-const lob_out_hole1 Int)
(declare-const lob_out_hole2 Int)
(declare-const lob_out_hole3 Int)
(declare-const bur_cor_hole0 Int)
(declare-const bur_cor_hole1 Int)
(declare-const bur_cor_hole2 Int)
(declare-const bur_cor_hole3 Int)
(declare-const mr_cor_hole0 Int)
(declare-const mr_cor_hole1 Int)
(declare-const mr_cor_hole2 Int)
(declare-const mr_cor_hole3 Int)
(declare-const cor_lob_hole0 Int)
(declare-const cor_lob_hole1 Int)
(declare-const cor_lob_hole2 Int)
(declare-const cor_lob_hole3 Int)
(declare-const cor_bur_hole0 Int)
(declare-const cor_bur_hole1 Int)
(declare-const cor_bur_hole2 Int)
(declare-const cor_bur_hole3 Int)
(declare-const cor_mr_hole0 Int)
(declare-const cor_mr_hole1 Int)
(declare-const cor_mr_hole2 Int)
(declare-const cor_mr_hole3 Int)
(declare-const cor_out_hole0 Int)
(declare-const cor_out_hole1 Int)
(declare-const cor_out_hole2 Int)
(declare-const cor_out_hole3 Int)
(declare-const out_lob_hole0 Int)
(declare-const out_lob_hole1 Int)
(declare-const out_lob_hole2 Int)
(declare-const out_lob_hole3 Int)
(declare-const out_cor_hole0 Int)
(declare-const out_cor_hole1 Int)
(declare-const out_cor_hole2 Int)
(declare-const out_cor_hole3 Int)
(define-fun from_to_hole ((from Room) (to Room) (i Int)) Int
  (if (and (= from lob) (= to cor) (= i 0)) lob_cor_hole0
  (if (and (= from lob) (= to cor) (= i 1)) lob_cor_hole1
  (if (and (= from lob) (= to cor) (= i 2)) lob_cor_hole2
  (if (and (= from lob) (= to cor) (= i 3)) lob_cor_hole3
  (if (and (= from lob) (= to out) (= i 0)) lob_out_hole0
  (if (and (= from lob) (= to out) (= i 1)) lob_out_hole1
  (if (and (= from lob) (= to out) (= i 2)) lob_out_hole2
  (if (and (= from lob) (= to out) (= i 3)) lob_out_hole3
  (if (and (= from bur) (= to cor) (= i 0)) bur_cor_hole0
  (if (and (= from bur) (= to cor) (= i 1)) bur_cor_hole1
  (if (and (= from bur) (= to cor) (= i 2)) bur_cor_hole2
  (if (and (= from bur) (= to cor) (= i 3)) bur_cor_hole3
  (if (and (= from mr) (= to cor) (= i 0)) mr_cor_hole0
  (if (and (= from mr) (= to cor) (= i 1)) mr_cor_hole1
  (if (and (= from mr) (= to cor) (= i 2)) mr_cor_hole2
  (if (and (= from mr) (= to cor) (= i 3)) mr_cor_hole3
  (if (and (= from cor) (= to lob) (= i 0)) cor_lob_hole0
  (if (and (= from cor) (= to lob) (= i 1)) cor_lob_hole1
  (if (and (= from cor) (= to lob) (= i 2)) cor_lob_hole2
  (if (and (= from cor) (= to lob) (= i 3)) cor_lob_hole3
  (if (and (= from cor) (= to bur) (= i 0)) cor_bur_hole0
  (if (and (= from cor) (= to bur) (= i 1)) cor_bur_hole1
  (if (and (= from cor) (= to bur) (= i 2)) cor_bur_hole2
  (if (and (= from cor) (= to bur) (= i 3)) cor_bur_hole3
  (if (and (= from cor) (= to mr) (= i 0)) cor_mr_hole0
  (if (and (= from cor) (= to mr) (= i 1)) cor_mr_hole1
  (if (and (= from cor) (= to mr) (= i 2)) cor_mr_hole2
  (if (and (= from cor) (= to mr) (= i 3)) cor_mr_hole3
  (if (and (= from cor) (= to out) (= i 0)) cor_out_hole0
  (if (and (= from cor) (= to out) (= i 1)) cor_out_hole1
  (if (and (= from cor) (= to out) (= i 2)) cor_out_hole2
  (if (and (= from cor) (= to out) (= i 3)) cor_out_hole3
  (if (and (= from out) (= to lob) (= i 0)) out_lob_hole0
  (if (and (= from out) (= to lob) (= i 1)) out_lob_hole1
  (if (and (= from out) (= to lob) (= i 2)) out_lob_hole2
  (if (and (= from out) (= to lob) (= i 3)) out_lob_hole3
  (if (and (= from out) (= to cor) (= i 0)) out_cor_hole0
  (if (and (= from out) (= to cor) (= i 1)) out_cor_hole1
  (if (and (= from out) (= to cor) (= i 2)) out_cor_hole2
  (if (and (= from out) (= to cor) (= i 3)) out_cor_hole3
  5)))))))))))))))))))))))))))))))))))))))))
(define-fun hole ((i Int) (visitor Bool) (employee Bool)) Bool
  (if (= i 0) visitor
  (if (= i 1) employee
  (if (= i 2) (not visitor)
  (if (= i 3) (not employee)
  (if (= i 4) true
  false))))))
(define-fun authz ((from Room) (to Room) (visitor Bool) (employee Bool)) Bool
  (or
    (and
      (hole (from_to_hole from to 0) visitor employee)
      (hole (from_to_hole from to 1) visitor employee)
    )
    (and
      (hole (from_to_hole from to 2) visitor employee)
      (hole (from_to_hole from to 3) visitor employee)
    )
    (= from to)
  )
)
