(declare-datatypes (T) (
    (Stream (event (value T))
            nothing)
))

(declare-datatypes () (
    (Unit unit)
))

(declare-datatypes () (
    (Counter (mk (output (Stream Int))
                 (value Int)
                 (clock  (Stream Unit))))
))

(declare-const Counter-0 (Array Int Counter))
(assert (= (clock (select Counter-0 0)) (as nothing (Stream Unit))))
(assert (= (clock (select Counter-0 1)) (event unit)))
(assert (= (clock (select Counter-0 2)) (event unit)))
(assert (= (clock (select Counter-0 3)) (event unit)))
(assert (= (clock (select Counter-0 4)) (event unit)))

(assert (= (value (select Counter-0 0)) 2))
(assert (= (value (select Counter-0 1)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 1))) (value (select Counter-0 0)) (+ 1 (value (select Counter-0 0))))))
(assert (= (value (select Counter-0 2)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 2))) (value (select Counter-0 1)) (+ 1 (value (select Counter-0 1))))))
(assert (= (value (select Counter-0 3)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 3))) (value (select Counter-0 2)) (+ 1 (value (select Counter-0 2))))))
(assert (= (value (select Counter-0 4)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 4))) (value (select Counter-0 3)) (+ 1 (value (select Counter-0 3))))))

(assert (= (output (select Counter-0 0)) (as nothing (Stream Int))))
(assert (= (output (select Counter-0 1)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 1))) (as nothing (Stream Int)) (event (value (select Counter-0 0))))))
(assert (= (output (select Counter-0 2)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 2))) (as nothing (Stream Int)) (event (value (select Counter-0 1))))))
(assert (= (output (select Counter-0 3)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 3))) (as nothing (Stream Int)) (event (value (select Counter-0 2))))))
(assert (= (output (select Counter-0 4)) (ite (= (as nothing (Stream Unit)) (clock (select Counter-0 4))) (as nothing (Stream Int)) (event (value (select Counter-0 3))))))

(declare-datatypes () 
   (
    (C      (mk-C  (out      Int)))
    (SS     (mk-SS (out      Int)))
    (Stage  (C     (c    C))
            (SS    (ss  SS)))))



;(declare-const b     Bool)
;(declare-const i      Int)
;(declare-const c        C)
;(declare-const ss      SS)
;(declare-const curr Stage)

;(define-fun stage-out ((s Stage)) Int
;    (if ((_ is C) s) 
;        (out (c s))
;        (out (ss s))))
                          
;(assert (= curr (ite b (C  (mk-C  5)) 
;                       (SS (mk-SS 6)))))

;(assert (= i (stage-out curr)))
;(assert (= i 6))

(declare-const c0 (Stream Int))
(declare-const c1 (Stream Int))
(declare-const c2 (Stream Int))
(declare-const c3 (Stream Int))
(declare-const c4 (Stream Int))

(assert (= c0 (output (select Counter-0 0))))
(assert (= c1 (output (select Counter-0 1))))
(assert (= c2 (output (select Counter-0 2))))
(assert (= c3 (output (select Counter-0 3))))
(assert (= c4 (output (select Counter-0 4))))

(check-sat)
(get-model)
