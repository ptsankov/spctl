(-> (& out (& visitor workhours)) (EF mr))
(-> (& out (! (| workhours pin))) (AG out))
;(-> (& out (& visitor workhours)) (EF lob))
;(-> (& out (& researcher workhours)) (EF cor1))
;(-> (& out (& it workhours)) (EF cor1))
;(-> (& out (& hr workhours)) (EF cor1))
(-> out (AG (-> mr (EF (| wc1 wc2)))))
(-> out (AG (-> (| bur1 (| bur6 bur7)) (! visitor))))
;(-> (-> out (EF bur6)) hr)
;(-> (& out (& postman workhours)) (EF post))
;(-> (& out (EF post)) postman)
;(-> (& postman post) (EF elev))
;(AG (-> (! (| hr postman)) (! (EF post))))
;(-> (& (& workhours out) (| postman hr)) (EF post))
;(-> (-> out (EF serv)) it)
;(-> (& workhours (& out it)) (EF serv))