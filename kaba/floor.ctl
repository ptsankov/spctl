(-> (& visitor workhours) (EF mr))
(-> (! (| workhours pin)) (AG out))
;(-> (& visitor workhours) (EF lob))
;(-> (& researcher workhours) (EF cor1))
;(-> (& it workhours) (EF cor1))
;(-> (& hr workhours) (EF cor1))
(AG (-> mr (EF (| wc1 wc2))))
(AG (-> (| bur1 (| bur6 bur7)) (! visitor)))
(AG (-> bur6 hr))
(-> (& postman workhours) (EF post))
(-> (& hr workhours) (EF post))
(-> (EF post) (| hr postman))
(-> (& it workhours) (EF serv))
(AG (-> serv it))
