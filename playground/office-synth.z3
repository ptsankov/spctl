(error "line 134 column 40: unknown constant !o")
sat
(model 
  ;; universe for Room:
  ;;   Room!val!0 Room!val!1 Room!val!4 Room!val!2 Room!val!3 
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun Room!val!0 () Room)
  (declare-fun Room!val!1 () Room)
  (declare-fun Room!val!4 () Room)
  (declare-fun Room!val!2 () Room)
  (declare-fun Room!val!3 () Room)
  ;; cardinality constraint:
  (forall ((x Room))
          (or (= x Room!val!0)
              (= x Room!val!1)
              (= x Room!val!4)
              (= x Room!val!2)
              (= x Room!val!3)))
  ;; -----------
  (define-fun authz_cor_out_noto_notv () Bool
    true)
  (define-fun authz_out_cor_o_notv () Bool
    true)
  (define-fun lob () Room
    Room!val!1)
  (define-fun authz_out_cor_noto_v () Bool
    false)
  (define-fun authz_cor_mr_noto_notv () Bool
    false)
  (define-fun authz_lob_out_o_notv () Bool
    true)
  (define-fun authz_out_lob_o_notv () Bool
    true)
  (define-fun authz_cor_out_noto_v () Bool
    true)
  (define-fun authz_mr_cor_o_v () Bool
    true)
  (define-fun authz_out_lob_o_v () Bool
    true)
  (define-fun authz_off_cor_o_v () Bool
    true)
  (define-fun authz_off_cor_noto_v () Bool
    true)
  (define-fun authz_cor_off_noto_notv () Bool
    false)
  (define-fun off () Room
    Room!val!3)
  (define-fun out () Room
    Room!val!0)
  (define-fun authz_cor_lob_noto_v () Bool
    true)
  (define-fun authz_lob_out_noto_notv () Bool
    true)
  (define-fun authz_cor_off_o_v () Bool
    true)
  (define-fun authz_out_lob_noto_notv () Bool
    false)
  (define-fun authz_cor_off_noto_v () Bool
    false)
  (define-fun authz_mr_cor_noto_v () Bool
    true)
  (define-fun authz_cor_out_o_v () Bool
    true)
  (define-fun authz_cor_lob_o_v () Bool
    true)
  (define-fun authz_cor_mr_o_v () Bool
    true)
  (define-fun authz_cor_off_o_notv () Bool
    true)
  (define-fun authz_cor_lob_noto_notv () Bool
    true)
  (define-fun authz_lob_cor_o_notv () Bool
    true)
  (define-fun authz_off_cor_noto_notv () Bool
    true)
  (define-fun authz_cor_lob_o_notv () Bool
    true)
  (define-fun authz_mr_cor_noto_notv () Bool
    true)
  (define-fun authz_out_cor_o_v () Bool
    false)
  (define-fun authz_out_cor_noto_notv () Bool
    false)
  (define-fun authz_lob_out_o_v () Bool
    true)
  (define-fun mr () Room
    Room!val!4)
  (define-fun authz_cor_mr_noto_v () Bool
    true)
  (define-fun authz_lob_cor_noto_notv () Bool
    false)
  (define-fun authz_lob_cor_o_v () Bool
    true)
  (define-fun authz_cor_mr_o_notv () Bool
    false)
  (define-fun authz_off_cor_o_notv () Bool
    true)
  (define-fun authz_cor_out_o_notv () Bool
    true)
  (define-fun authz_out_lob_noto_v () Bool
    true)
  (define-fun authz_lob_out_noto_v () Bool
    true)
  (define-fun authz_lob_cor_noto_v () Bool
    true)
  (define-fun cor () Room
    Room!val!2)
  (define-fun authz_mr_cor_o_notv () Bool
    true)
  (define-fun k!0 ((x!1 Bool)) Bool
    (ite (= x!1 false) false
      true))
  (define-fun k!1 ((x!1 Bool)) Bool
    (ite (= x!1 false) false
      true))
  (define-fun authz!2 ((x!1 Room) (x!2 Room) (x!3 Bool) (x!4 Bool)) Bool
    (ite (and (= x!1 Room!val!0) (= x!2 Room!val!1) (= x!3 false) (= x!4 false))
      false
    (ite (and (= x!1 Room!val!0) (= x!2 Room!val!2) (= x!3 true) (= x!4 true))
      false
    (ite (and (= x!1 Room!val!0) (= x!2 Room!val!2) (= x!3 false) (= x!4 true))
      false
    (ite (and (= x!1 Room!val!0) (= x!2 Room!val!2) (= x!3 false) (= x!4 false))
      false
    (ite (and (= x!1 Room!val!1) (= x!2 Room!val!2) (= x!3 false) (= x!4 false))
      false
    (ite (and (= x!1 Room!val!2) (= x!2 Room!val!3) (= x!3 false) (= x!4 true))
      false
    (ite (and (= x!1 Room!val!2) (= x!2 Room!val!3) (= x!3 false) (= x!4 false))
      false
    (ite (and (= x!1 Room!val!2) (= x!2 Room!val!4) (= x!3 true) (= x!4 false))
      false
    (ite (and (= x!1 Room!val!2) (= x!2 Room!val!4) (= x!3 false) (= x!4 false))
      false
      true))))))))))
  (define-fun authz ((x!1 Room) (x!2 Room) (x!3 Bool) (x!4 Bool)) Bool
    (authz!2 x!1 x!2 (k!1 x!3) (k!0 x!4)))
)
