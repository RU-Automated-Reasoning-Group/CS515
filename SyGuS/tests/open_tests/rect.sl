(set-logic LIA)

(synth-fun f ((x0 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int
   ((Start Int (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 x0 x1 x2 x3 x4
                 (+ Start Start)
                 (- Start Start)
                 (* Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)
                      (< Start Start)
                      (> Start Start)))))

(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)

(constraint (=> (and (< x4 32) (and (>= x4 0) (and (< x3 32) (and (>= x3 0) (and (< x2 32) (and (>= x2 0) (and (< x1 32) (and (>= x1 0) (and (< x0 32) (>= x0 0)))))))))) (and (and (>= (f x0 x1 x2 x3 x4) 0) (<= (f x0 x1 x2 x3 x4) 31)) (and (iff (<= x4 12) (or (= (f x0 x1 x2 x3 x4) 16) (or (= (f x0 x1 x2 x3 x4) 9) (or (= (f x0 x1 x2 x3 x4) 30) (or (= (f x0 x1 x2 x3 x4) 28) (or (= (f x0 x1 x2 x3 x4) 14) (or (= (f x0 x1 x2 x3 x4) 4) (or (= (f x0 x1 x2 x3 x4) 21) (or (= (f x0 x1 x2 x3 x4) 23) (or (= (f x0 x1 x2 x3 x4) 5) (or (= (f x0 x1 x2 x3 x4) 12) (or (= (f x0 x1 x2 x3 x4) 29) (or (= (f x0 x1 x2 x3 x4) 13) (or (= (f x0 x1 x2 x3 x4) 11) (or (= (f x0 x1 x2 x3 x4) 22) (or (= (f x0 x1 x2 x3 x4) 27) (= (f x0 x1 x2 x3 x4) 0))))))))))))))))) (and (iff (<= x3 29) (or (= (f x0 x1 x2 x3 x4) 19) (or (= (f x0 x1 x2 x3 x4) 8) (or (= (f x0 x1 x2 x3 x4) 26) (or (= (f x0 x1 x2 x3 x4) 20) (or (= (f x0 x1 x2 x3 x4) 17) (or (= (f x0 x1 x2 x3 x4) 10) (or (= (f x0 x1 x2 x3 x4) 31) (or (= (f x0 x1 x2 x3 x4) 7) (or (= (f x0 x1 x2 x3 x4) 5) (or (= (f x0 x1 x2 x3 x4) 12) (or (= (f x0 x1 x2 x3 x4) 29) (or (= (f x0 x1 x2 x3 x4) 13) (or (= (f x0 x1 x2 x3 x4) 11) (or (= (f x0 x1 x2 x3 x4) 22) (or (= (f x0 x1 x2 x3 x4) 27) (= (f x0 x1 x2 x3 x4) 0))))))))))))))))) (and (iff (<= x2 20) (or (= (f x0 x1 x2 x3 x4) 3) (or (= (f x0 x1 x2 x3 x4) 1) (or (= (f x0 x1 x2 x3 x4) 25) (or (= (f x0 x1 x2 x3 x4) 6) (or (= (f x0 x1 x2 x3 x4) 17) (or (= (f x0 x1 x2 x3 x4) 10) (or (= (f x0 x1 x2 x3 x4) 31) (or (= (f x0 x1 x2 x3 x4) 7) (or (= (f x0 x1 x2 x3 x4) 14) (or (= (f x0 x1 x2 x3 x4) 4) (or (= (f x0 x1 x2 x3 x4) 21) (or (= (f x0 x1 x2 x3 x4) 23) (or (= (f x0 x1 x2 x3 x4) 11) (or (= (f x0 x1 x2 x3 x4) 22) (or (= (f x0 x1 x2 x3 x4) 27) (= (f x0 x1 x2 x3 x4) 0))))))))))))))))) (and (iff (<= x1 6) (or (= (f x0 x1 x2 x3 x4) 2) (or (= (f x0 x1 x2 x3 x4) 15) (or (= (f x0 x1 x2 x3 x4) 25) (or (= (f x0 x1 x2 x3 x4) 6) (or (= (f x0 x1 x2 x3 x4) 26) (or (= (f x0 x1 x2 x3 x4) 20) (or (= (f x0 x1 x2 x3 x4) 31) (or (= (f x0 x1 x2 x3 x4) 7) (or (= (f x0 x1 x2 x3 x4) 30) (or (= (f x0 x1 x2 x3 x4) 28) (or (= (f x0 x1 x2 x3 x4) 21) (or (= (f x0 x1 x2 x3 x4) 23) (or (= (f x0 x1 x2 x3 x4) 29) (or (= (f x0 x1 x2 x3 x4) 13) (or (= (f x0 x1 x2 x3 x4) 27) (= (f x0 x1 x2 x3 x4) 0))))))))))))))))) (iff (<= x0 5) (or (= (f x0 x1 x2 x3 x4) 18) (or (= (f x0 x1 x2 x3 x4) 15) (or (= (f x0 x1 x2 x3 x4) 1) (or (= (f x0 x1 x2 x3 x4) 6) (or (= (f x0 x1 x2 x3 x4) 8) (or (= (f x0 x1 x2 x3 x4) 20) (or (= (f x0 x1 x2 x3 x4) 10) (or (= (f x0 x1 x2 x3 x4) 7) (or (= (f x0 x1 x2 x3 x4) 9) (or (= (f x0 x1 x2 x3 x4) 28) (or (= (f x0 x1 x2 x3 x4) 4) (or (= (f x0 x1 x2 x3 x4) 23) (or (= (f x0 x1 x2 x3 x4) 12) (or (= (f x0 x1 x2 x3 x4) 13) (or (= (f x0 x1 x2 x3 x4) 22) (= (f x0 x1 x2 x3 x4) 0))))))))))))))))))))))))


(check-synth)

