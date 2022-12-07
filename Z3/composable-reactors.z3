(declare-datatypes (T) ((Stream (event (value T))
                                nothing)))

(declare-const s1 (Stream Int))
(assert (not (= s1 nothing)))
(check-sat)
(get-model)


