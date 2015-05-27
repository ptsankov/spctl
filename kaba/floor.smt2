(declare-sort Room)
(declare-const lob Room)
(declare-const wc1 Room)
(declare-const wc2 Room)
(declare-const elev Room)
(declare-const serv Room)
(declare-const cor3 Room)
(declare-const bur7 Room)
(declare-const bur6 Room)
(declare-const bur1 Room)
(declare-const cor1 Room)
(declare-const cor2 Room)
(declare-const mr Room)
(declare-const post Room)
(declare-const out Room)
(assert (distinct lob wc1 wc2 elev serv cor3 bur7 bur6 bur1 cor1 cor2 mr post out))
(assert (forall ((r Room)) (or (= r lob) (= r wc1) (= r wc2) (= r elev) (= r serv) (= r cor3) (= r bur7) (= r bur6) (= r bur1) (= r cor1) (= r cor2) (= r mr) (= r post) (= r out))))
(declare-const lob_cor1_hole0 Int)
(declare-const lob_cor1_hole1 Int)
(declare-const lob_cor1_hole2 Int)
(declare-const lob_cor1_hole3 Int)
(declare-const lob_mr_hole0 Int)
(declare-const lob_mr_hole1 Int)
(declare-const lob_mr_hole2 Int)
(declare-const lob_mr_hole3 Int)
(declare-const wc1_cor1_hole0 Int)
(declare-const wc1_cor1_hole1 Int)
(declare-const wc1_cor1_hole2 Int)
(declare-const wc1_cor1_hole3 Int)
(declare-const wc2_cor1_hole0 Int)
(declare-const wc2_cor1_hole1 Int)
(declare-const wc2_cor1_hole2 Int)
(declare-const wc2_cor1_hole3 Int)
(declare-const serv_cor2_hole0 Int)
(declare-const serv_cor2_hole1 Int)
(declare-const serv_cor2_hole2 Int)
(declare-const serv_cor2_hole3 Int)
(declare-const cor3_cor1_hole0 Int)
(declare-const cor3_cor1_hole1 Int)
(declare-const cor3_cor1_hole2 Int)
(declare-const cor3_cor1_hole3 Int)
(declare-const cor3_out_hole0 Int)
(declare-const cor3_out_hole1 Int)
(declare-const cor3_out_hole2 Int)
(declare-const cor3_out_hole3 Int)
(declare-const bur7_cor1_hole0 Int)
(declare-const bur7_cor1_hole1 Int)
(declare-const bur7_cor1_hole2 Int)
(declare-const bur7_cor1_hole3 Int)
(declare-const bur6_cor1_hole0 Int)
(declare-const bur6_cor1_hole1 Int)
(declare-const bur6_cor1_hole2 Int)
(declare-const bur6_cor1_hole3 Int)
(declare-const bur1_cor1_hole0 Int)
(declare-const bur1_cor1_hole1 Int)
(declare-const bur1_cor1_hole2 Int)
(declare-const bur1_cor1_hole3 Int)
(declare-const cor1_lob_hole0 Int)
(declare-const cor1_lob_hole1 Int)
(declare-const cor1_lob_hole2 Int)
(declare-const cor1_lob_hole3 Int)
(declare-const cor1_wc1_hole0 Int)
(declare-const cor1_wc1_hole1 Int)
(declare-const cor1_wc1_hole2 Int)
(declare-const cor1_wc1_hole3 Int)
(declare-const cor1_wc2_hole0 Int)
(declare-const cor1_wc2_hole1 Int)
(declare-const cor1_wc2_hole2 Int)
(declare-const cor1_wc2_hole3 Int)
(declare-const cor1_bur7_hole0 Int)
(declare-const cor1_bur7_hole1 Int)
(declare-const cor1_bur7_hole2 Int)
(declare-const cor1_bur7_hole3 Int)
(declare-const cor1_bur6_hole0 Int)
(declare-const cor1_bur6_hole1 Int)
(declare-const cor1_bur6_hole2 Int)
(declare-const cor1_bur6_hole3 Int)
(declare-const cor1_bur1_hole0 Int)
(declare-const cor1_bur1_hole1 Int)
(declare-const cor1_bur1_hole2 Int)
(declare-const cor1_bur1_hole3 Int)
(declare-const cor1_cor3_hole0 Int)
(declare-const cor1_cor3_hole1 Int)
(declare-const cor1_cor3_hole2 Int)
(declare-const cor1_cor3_hole3 Int)
(declare-const cor1_post_hole0 Int)
(declare-const cor1_post_hole1 Int)
(declare-const cor1_post_hole2 Int)
(declare-const cor1_post_hole3 Int)
(declare-const cor1_out_hole0 Int)
(declare-const cor1_out_hole1 Int)
(declare-const cor1_out_hole2 Int)
(declare-const cor1_out_hole3 Int)
(declare-const cor2_serv_hole0 Int)
(declare-const cor2_serv_hole1 Int)
(declare-const cor2_serv_hole2 Int)
(declare-const cor2_serv_hole3 Int)
(declare-const cor2_post_hole0 Int)
(declare-const cor2_post_hole1 Int)
(declare-const cor2_post_hole2 Int)
(declare-const cor2_post_hole3 Int)
(declare-const cor2_elev_hole0 Int)
(declare-const cor2_elev_hole1 Int)
(declare-const cor2_elev_hole2 Int)
(declare-const cor2_elev_hole3 Int)
(declare-const cor2_out_hole0 Int)
(declare-const cor2_out_hole1 Int)
(declare-const cor2_out_hole2 Int)
(declare-const cor2_out_hole3 Int)
(declare-const mr_lob_hole0 Int)
(declare-const mr_lob_hole1 Int)
(declare-const mr_lob_hole2 Int)
(declare-const mr_lob_hole3 Int)
(declare-const post_cor1_hole0 Int)
(declare-const post_cor1_hole1 Int)
(declare-const post_cor1_hole2 Int)
(declare-const post_cor1_hole3 Int)
(declare-const post_cor2_hole0 Int)
(declare-const post_cor2_hole1 Int)
(declare-const post_cor2_hole2 Int)
(declare-const post_cor2_hole3 Int)
(declare-const out_lob_hole0 Int)
(declare-const out_lob_hole1 Int)
(declare-const out_lob_hole2 Int)
(declare-const out_lob_hole3 Int)
(declare-const out_cor2_hole0 Int)
(declare-const out_cor2_hole1 Int)
(declare-const out_cor2_hole2 Int)
(declare-const out_cor2_hole3 Int)
(declare-const out_cor3_hole0 Int)
(declare-const out_cor3_hole1 Int)
(declare-const out_cor3_hole2 Int)
(declare-const out_cor3_hole3 Int)
(define-fun from_to_hole ((from Room) (to Room) (i Int)) Int
  (if (and (= from lob) (= to cor1) (= i 0)) lob_cor1_hole0
  (if (and (= from lob) (= to cor1) (= i 1)) lob_cor1_hole1
  (if (and (= from lob) (= to cor1) (= i 2)) lob_cor1_hole2
  (if (and (= from lob) (= to cor1) (= i 3)) lob_cor1_hole3
  (if (and (= from lob) (= to mr) (= i 0)) lob_mr_hole0
  (if (and (= from lob) (= to mr) (= i 1)) lob_mr_hole1
  (if (and (= from lob) (= to mr) (= i 2)) lob_mr_hole2
  (if (and (= from lob) (= to mr) (= i 3)) lob_mr_hole3
  (if (and (= from wc1) (= to cor1) (= i 0)) wc1_cor1_hole0
  (if (and (= from wc1) (= to cor1) (= i 1)) wc1_cor1_hole1
  (if (and (= from wc1) (= to cor1) (= i 2)) wc1_cor1_hole2
  (if (and (= from wc1) (= to cor1) (= i 3)) wc1_cor1_hole3
  (if (and (= from wc2) (= to cor1) (= i 0)) wc2_cor1_hole0
  (if (and (= from wc2) (= to cor1) (= i 1)) wc2_cor1_hole1
  (if (and (= from wc2) (= to cor1) (= i 2)) wc2_cor1_hole2
  (if (and (= from wc2) (= to cor1) (= i 3)) wc2_cor1_hole3
  (if (and (= from serv) (= to cor2) (= i 0)) serv_cor2_hole0
  (if (and (= from serv) (= to cor2) (= i 1)) serv_cor2_hole1
  (if (and (= from serv) (= to cor2) (= i 2)) serv_cor2_hole2
  (if (and (= from serv) (= to cor2) (= i 3)) serv_cor2_hole3
  (if (and (= from cor3) (= to cor1) (= i 0)) cor3_cor1_hole0
  (if (and (= from cor3) (= to cor1) (= i 1)) cor3_cor1_hole1
  (if (and (= from cor3) (= to cor1) (= i 2)) cor3_cor1_hole2
  (if (and (= from cor3) (= to cor1) (= i 3)) cor3_cor1_hole3
  (if (and (= from cor3) (= to out) (= i 0)) cor3_out_hole0
  (if (and (= from cor3) (= to out) (= i 1)) cor3_out_hole1
  (if (and (= from cor3) (= to out) (= i 2)) cor3_out_hole2
  (if (and (= from cor3) (= to out) (= i 3)) cor3_out_hole3
  (if (and (= from bur7) (= to cor1) (= i 0)) bur7_cor1_hole0
  (if (and (= from bur7) (= to cor1) (= i 1)) bur7_cor1_hole1
  (if (and (= from bur7) (= to cor1) (= i 2)) bur7_cor1_hole2
  (if (and (= from bur7) (= to cor1) (= i 3)) bur7_cor1_hole3
  (if (and (= from bur6) (= to cor1) (= i 0)) bur6_cor1_hole0
  (if (and (= from bur6) (= to cor1) (= i 1)) bur6_cor1_hole1
  (if (and (= from bur6) (= to cor1) (= i 2)) bur6_cor1_hole2
  (if (and (= from bur6) (= to cor1) (= i 3)) bur6_cor1_hole3
  (if (and (= from bur1) (= to cor1) (= i 0)) bur1_cor1_hole0
  (if (and (= from bur1) (= to cor1) (= i 1)) bur1_cor1_hole1
  (if (and (= from bur1) (= to cor1) (= i 2)) bur1_cor1_hole2
  (if (and (= from bur1) (= to cor1) (= i 3)) bur1_cor1_hole3
  (if (and (= from cor1) (= to lob) (= i 0)) cor1_lob_hole0
  (if (and (= from cor1) (= to lob) (= i 1)) cor1_lob_hole1
  (if (and (= from cor1) (= to lob) (= i 2)) cor1_lob_hole2
  (if (and (= from cor1) (= to lob) (= i 3)) cor1_lob_hole3
  (if (and (= from cor1) (= to wc1) (= i 0)) cor1_wc1_hole0
  (if (and (= from cor1) (= to wc1) (= i 1)) cor1_wc1_hole1
  (if (and (= from cor1) (= to wc1) (= i 2)) cor1_wc1_hole2
  (if (and (= from cor1) (= to wc1) (= i 3)) cor1_wc1_hole3
  (if (and (= from cor1) (= to wc2) (= i 0)) cor1_wc2_hole0
  (if (and (= from cor1) (= to wc2) (= i 1)) cor1_wc2_hole1
  (if (and (= from cor1) (= to wc2) (= i 2)) cor1_wc2_hole2
  (if (and (= from cor1) (= to wc2) (= i 3)) cor1_wc2_hole3
  (if (and (= from cor1) (= to bur7) (= i 0)) cor1_bur7_hole0
  (if (and (= from cor1) (= to bur7) (= i 1)) cor1_bur7_hole1
  (if (and (= from cor1) (= to bur7) (= i 2)) cor1_bur7_hole2
  (if (and (= from cor1) (= to bur7) (= i 3)) cor1_bur7_hole3
  (if (and (= from cor1) (= to bur6) (= i 0)) cor1_bur6_hole0
  (if (and (= from cor1) (= to bur6) (= i 1)) cor1_bur6_hole1
  (if (and (= from cor1) (= to bur6) (= i 2)) cor1_bur6_hole2
  (if (and (= from cor1) (= to bur6) (= i 3)) cor1_bur6_hole3
  (if (and (= from cor1) (= to bur1) (= i 0)) cor1_bur1_hole0
  (if (and (= from cor1) (= to bur1) (= i 1)) cor1_bur1_hole1
  (if (and (= from cor1) (= to bur1) (= i 2)) cor1_bur1_hole2
  (if (and (= from cor1) (= to bur1) (= i 3)) cor1_bur1_hole3
  (if (and (= from cor1) (= to cor3) (= i 0)) cor1_cor3_hole0
  (if (and (= from cor1) (= to cor3) (= i 1)) cor1_cor3_hole1
  (if (and (= from cor1) (= to cor3) (= i 2)) cor1_cor3_hole2
  (if (and (= from cor1) (= to cor3) (= i 3)) cor1_cor3_hole3
  (if (and (= from cor1) (= to post) (= i 0)) cor1_post_hole0
  (if (and (= from cor1) (= to post) (= i 1)) cor1_post_hole1
  (if (and (= from cor1) (= to post) (= i 2)) cor1_post_hole2
  (if (and (= from cor1) (= to post) (= i 3)) cor1_post_hole3
  (if (and (= from cor1) (= to out) (= i 0)) cor1_out_hole0
  (if (and (= from cor1) (= to out) (= i 1)) cor1_out_hole1
  (if (and (= from cor1) (= to out) (= i 2)) cor1_out_hole2
  (if (and (= from cor1) (= to out) (= i 3)) cor1_out_hole3
  (if (and (= from cor2) (= to serv) (= i 0)) cor2_serv_hole0
  (if (and (= from cor2) (= to serv) (= i 1)) cor2_serv_hole1
  (if (and (= from cor2) (= to serv) (= i 2)) cor2_serv_hole2
  (if (and (= from cor2) (= to serv) (= i 3)) cor2_serv_hole3
  (if (and (= from cor2) (= to post) (= i 0)) cor2_post_hole0
  (if (and (= from cor2) (= to post) (= i 1)) cor2_post_hole1
  (if (and (= from cor2) (= to post) (= i 2)) cor2_post_hole2
  (if (and (= from cor2) (= to post) (= i 3)) cor2_post_hole3
  (if (and (= from cor2) (= to elev) (= i 0)) cor2_elev_hole0
  (if (and (= from cor2) (= to elev) (= i 1)) cor2_elev_hole1
  (if (and (= from cor2) (= to elev) (= i 2)) cor2_elev_hole2
  (if (and (= from cor2) (= to elev) (= i 3)) cor2_elev_hole3
  (if (and (= from cor2) (= to out) (= i 0)) cor2_out_hole0
  (if (and (= from cor2) (= to out) (= i 1)) cor2_out_hole1
  (if (and (= from cor2) (= to out) (= i 2)) cor2_out_hole2
  (if (and (= from cor2) (= to out) (= i 3)) cor2_out_hole3
  (if (and (= from mr) (= to lob) (= i 0)) mr_lob_hole0
  (if (and (= from mr) (= to lob) (= i 1)) mr_lob_hole1
  (if (and (= from mr) (= to lob) (= i 2)) mr_lob_hole2
  (if (and (= from mr) (= to lob) (= i 3)) mr_lob_hole3
  (if (and (= from post) (= to cor1) (= i 0)) post_cor1_hole0
  (if (and (= from post) (= to cor1) (= i 1)) post_cor1_hole1
  (if (and (= from post) (= to cor1) (= i 2)) post_cor1_hole2
  (if (and (= from post) (= to cor1) (= i 3)) post_cor1_hole3
  (if (and (= from post) (= to cor2) (= i 0)) post_cor2_hole0
  (if (and (= from post) (= to cor2) (= i 1)) post_cor2_hole1
  (if (and (= from post) (= to cor2) (= i 2)) post_cor2_hole2
  (if (and (= from post) (= to cor2) (= i 3)) post_cor2_hole3
  (if (and (= from out) (= to lob) (= i 0)) out_lob_hole0
  (if (and (= from out) (= to lob) (= i 1)) out_lob_hole1
  (if (and (= from out) (= to lob) (= i 2)) out_lob_hole2
  (if (and (= from out) (= to lob) (= i 3)) out_lob_hole3
  (if (and (= from out) (= to cor2) (= i 0)) out_cor2_hole0
  (if (and (= from out) (= to cor2) (= i 1)) out_cor2_hole1
  (if (and (= from out) (= to cor2) (= i 2)) out_cor2_hole2
  (if (and (= from out) (= to cor2) (= i 3)) out_cor2_hole3
  (if (and (= from out) (= to cor3) (= i 0)) out_cor3_hole0
  (if (and (= from out) (= to cor3) (= i 1)) out_cor3_hole1
  (if (and (= from out) (= to cor3) (= i 2)) out_cor3_hole2
  (if (and (= from out) (= to cor3) (= i 3)) out_cor3_hole3
  15)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(define-fun hole ((i Int) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (if (= i 0) pin
  (if (= i 1) visitor
  (if (= i 2) researcher
  (if (= i 3) hr
  (if (= i 4) postman
  (if (= i 5) it
  (if (= i 6) workhours
  (if (= i 7) (not pin)
  (if (= i 8) (not visitor)
  (if (= i 9) (not researcher)
  (if (= i 10) (not hr)
  (if (= i 11) (not postman)
  (if (= i 12) (not it)
  (if (= i 13) (not workhours)
  (if (= i 14) true
  false))))))))))))))))
(define-fun authz ((from Room) (to Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (and
      (hole (from_to_hole from to 0) pin visitor researcher hr postman it workhours)
      (hole (from_to_hole from to 1) pin visitor researcher hr postman it workhours)
    )
    (and
      (hole (from_to_hole from to 2) pin visitor researcher hr postman it workhours)
      (hole (from_to_hole from to 3) pin visitor researcher hr postman it workhours)
    )
    (= from to)
  )
)
(define-fun fun_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool visitor)
(define-fun fun_workhours ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool workhours)
(define-fun and_visitor_workhours ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (and (fun_visitor room0 pin visitor researcher hr postman it workhours) (fun_workhours room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_true ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool true)
(define-fun fun_mr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 mr))
(define-fun EU_fun_true_mr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (fun_mr room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_mr room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_mr room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (fun_mr room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_mr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_mr room0 pin visitor researcher hr postman it workhours))
(define-fun implies_and_visitor_workhours_EF_mr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (and_visitor_workhours room0 pin visitor researcher hr postman it workhours) (EF_mr room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_pin ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool pin)
(define-fun or_workhours_pin ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (or (fun_workhours room0 pin visitor researcher hr postman it workhours) (fun_pin room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_or_workhours_pin ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (or_workhours_pin room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 out))
(define-fun neg_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (fun_out room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_neg_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (neg_out room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (neg_out room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (neg_out room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (neg_out room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_neg_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_neg_out room0 pin visitor researcher hr postman it workhours))
(define-fun neg_EF_neg_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (EF_neg_out room0 pin visitor researcher hr postman it workhours)))
(define-fun AG_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (neg_EF_neg_out room0 pin visitor researcher hr postman it workhours))
(define-fun implies_neg_or_workhours_pin_AG_out ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (neg_or_workhours_pin room0 pin visitor researcher hr postman it workhours) (AG_out room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_wc1 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 wc1))
(define-fun fun_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 wc2))
(define-fun or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (or (fun_wc1 room0 pin visitor researcher hr postman it workhours) (fun_wc2 room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (or_wc1_wc2 room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (or_wc1_wc2 room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (or_wc1_wc2 room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (or_wc1_wc2 room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours))
(define-fun implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (fun_mr room0 pin visitor researcher hr postman it workhours) (EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (implies_mr_EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_neg_implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (neg_implies_mr_EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (neg_implies_mr_EF_or_wc1_wc2 room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (neg_implies_mr_EF_or_wc1_wc2 room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (neg_implies_mr_EF_or_wc1_wc2 room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_neg_implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_neg_implies_mr_EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours))
(define-fun neg_EF_neg_implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (EF_neg_implies_mr_EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours)))
(define-fun AG_implies_mr_EF_or_wc1_wc2 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (neg_EF_neg_implies_mr_EF_or_wc1_wc2 room0 pin visitor researcher hr postman it workhours))
(define-fun fun_bur1 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 bur1))
(define-fun fun_bur6 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 bur6))
(define-fun fun_bur7 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 bur7))
(define-fun or_bur6_bur7 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (or (fun_bur6 room0 pin visitor researcher hr postman it workhours) (fun_bur7 room0 pin visitor researcher hr postman it workhours)))
(define-fun or_bur1_or_bur6_bur7 ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (or (fun_bur1 room0 pin visitor researcher hr postman it workhours) (or_bur6_bur7 room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (fun_visitor room0 pin visitor researcher hr postman it workhours)))
(define-fun implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (or_bur1_or_bur6_bur7 room0 pin visitor researcher hr postman it workhours) (neg_visitor room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (implies_or_bur1_or_bur6_bur7_neg_visitor room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_neg_implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (neg_implies_or_bur1_or_bur6_bur7_neg_visitor room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (neg_implies_or_bur1_or_bur6_bur7_neg_visitor room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (neg_implies_or_bur1_or_bur6_bur7_neg_visitor room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (neg_implies_or_bur1_or_bur6_bur7_neg_visitor room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_neg_implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_neg_implies_or_bur1_or_bur6_bur7_neg_visitor room0 pin visitor researcher hr postman it workhours))
(define-fun neg_EF_neg_implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (EF_neg_implies_or_bur1_or_bur6_bur7_neg_visitor room0 pin visitor researcher hr postman it workhours)))
(define-fun AG_implies_or_bur1_or_bur6_bur7_neg_visitor ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (neg_EF_neg_implies_or_bur1_or_bur6_bur7_neg_visitor room0 pin visitor researcher hr postman it workhours))
(define-fun fun_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool hr)
(define-fun implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (fun_bur6 room0 pin visitor researcher hr postman it workhours) (fun_hr room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (implies_bur6_hr room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_neg_implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (neg_implies_bur6_hr room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (neg_implies_bur6_hr room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (neg_implies_bur6_hr room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (neg_implies_bur6_hr room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_neg_implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_neg_implies_bur6_hr room0 pin visitor researcher hr postman it workhours))
(define-fun neg_EF_neg_implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (EF_neg_implies_bur6_hr room0 pin visitor researcher hr postman it workhours)))
(define-fun AG_implies_bur6_hr ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (neg_EF_neg_implies_bur6_hr room0 pin visitor researcher hr postman it workhours))
(define-fun fun_postman ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool postman)
(define-fun and_postman_workhours ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (and (fun_postman room0 pin visitor researcher hr postman it workhours) (fun_workhours room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_post ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 post))
(define-fun EU_fun_true_post ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (fun_post room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_post room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_post room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (fun_post room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_post ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_post room0 pin visitor researcher hr postman it workhours))
(define-fun implies_and_postman_workhours_EF_post ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (and_postman_workhours room0 pin visitor researcher hr postman it workhours) (EF_post room0 pin visitor researcher hr postman it workhours)))
(define-fun and_hr_workhours ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (and (fun_hr room0 pin visitor researcher hr postman it workhours) (fun_workhours room0 pin visitor researcher hr postman it workhours)))
(define-fun implies_and_hr_workhours_EF_post ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (and_hr_workhours room0 pin visitor researcher hr postman it workhours) (EF_post room0 pin visitor researcher hr postman it workhours)))
(define-fun or_hr_postman ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (or (fun_hr room0 pin visitor researcher hr postman it workhours) (fun_postman room0 pin visitor researcher hr postman it workhours)))
(define-fun implies_EF_post_or_hr_postman ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (EF_post room0 pin visitor researcher hr postman it workhours) (or_hr_postman room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool it)
(define-fun and_it_workhours ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (and (fun_it room0 pin visitor researcher hr postman it workhours) (fun_workhours room0 pin visitor researcher hr postman it workhours)))
(define-fun fun_serv ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (= room0 serv))
(define-fun EU_fun_true_serv ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (fun_serv room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_serv room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_serv room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (fun_serv room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_serv ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_serv room0 pin visitor researcher hr postman it workhours))
(define-fun implies_and_it_workhours_EF_serv ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (and_it_workhours room0 pin visitor researcher hr postman it workhours) (EF_serv room0 pin visitor researcher hr postman it workhours)))
(define-fun implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (=> (fun_serv room0 pin visitor researcher hr postman it workhours) (fun_it room0 pin visitor researcher hr postman it workhours)))
(define-fun neg_implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (implies_serv_it room0 pin visitor researcher hr postman it workhours)))
(define-fun EU_fun_true_neg_implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool
  (or
    (neg_implies_serv_it room0 pin visitor researcher hr postman it workhours)
    (exists ((room1 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (neg_implies_serv_it room1 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (neg_implies_serv_it room2 pin visitor researcher hr postman it workhours)))
    (exists ((room1 Room) (room2 Room) (room3 Room)) (and (authz room0 room1 pin visitor researcher hr postman it workhours) (authz room1 room2 pin visitor researcher hr postman it workhours) (authz room2 room3 pin visitor researcher hr postman it workhours) (fun_true room0 pin visitor researcher hr postman it workhours) (fun_true room1 pin visitor researcher hr postman it workhours) (fun_true room2 pin visitor researcher hr postman it workhours) (neg_implies_serv_it room3 pin visitor researcher hr postman it workhours)))
  )
)
(define-fun EF_neg_implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (EU_fun_true_neg_implies_serv_it room0 pin visitor researcher hr postman it workhours))
(define-fun neg_EF_neg_implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (not (EF_neg_implies_serv_it room0 pin visitor researcher hr postman it workhours)))
(define-fun AG_implies_serv_it ((room0 Room) (pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool)) Bool (neg_EF_neg_implies_serv_it room0 pin visitor researcher hr postman it workhours))
(assert
  (forall ((pin Bool) (visitor Bool) (researcher Bool) (hr Bool) (postman Bool) (it Bool) (workhours Bool))
    (and
        (implies_and_visitor_workhours_EF_mr out pin visitor researcher hr postman it workhours)
        (implies_neg_or_workhours_pin_AG_out out pin visitor researcher hr postman it workhours)
        (AG_implies_mr_EF_or_wc1_wc2 out pin visitor researcher hr postman it workhours)
        (AG_implies_or_bur1_or_bur6_bur7_neg_visitor out pin visitor researcher hr postman it workhours)
        (AG_implies_bur6_hr out pin visitor researcher hr postman it workhours)
        (implies_and_postman_workhours_EF_post out pin visitor researcher hr postman it workhours)
        (implies_and_hr_workhours_EF_post out pin visitor researcher hr postman it workhours)
        (implies_EF_post_or_hr_postman out pin visitor researcher hr postman it workhours)
        (implies_and_it_workhours_EF_serv out pin visitor researcher hr postman it workhours)
        (AG_implies_serv_it out pin visitor researcher hr postman it workhours)
    )
  )
)
