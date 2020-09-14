# SyGuS

## Algorithm 1: Baseline (top-down enumeration):

python3 ./programs/baseline/main.py ./tests/open_tests/max2.sl

## Algorithm 2: Decision Tree:

python3 ./programs/decisiontree/main.py ./tests/open_tests/array_search_15.sl

```lisp
(define-fun findIdx ((y1 Int) (y2 Int) (y3 Int) (y4 Int) (y5 Int) (y6 Int) (y7 Int) (y8 Int) (y9 Int) (y10 Int) (y11 Int) (y12 Int) (y13 Int) (y14 Int) (y15 Int) (k1 Int)) Int
    (ite (< k1 y8)
        (ite (< k1 y4)
            (ite (< k1 y2)
                (ite (< k1 y1) 0 1)
                (ite (< k1 y3) 2 3))
            (ite (< k1 y6)
                (ite (< k1 y5) 4 5)
                (ite (< k1 y7) 6 7)))
        (ite (< y12 k1)
            (ite (< k1 y14)
                (ite (< k1 y13) 12 13)
                (ite (< k1 y15) 14 15))
            (ite (< k1 y10)
                (ite (< k1 y9) 8 9)
                (ite (< k1 y11) 10 11)))))
```

## Algorithm 3: (a bit similar to the EU-Solver):

python3 ./programs/eu-like/main.py ./tests/open_tests/max6.sl

   ```scheme
   (define-fun max6 ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int)) Int (ite (and (and (and (and (<= x2 x1) (<= x3 x1)) (<= x4 x1)) (<= x5 x1)) (<= x6 x1)) x1 (ite (and (and (and (<= x3 x2) (<= x4 x2)) (<= x5 x2)) (<= x6 x2)) x2 (ite (and (and (<= x4 x3) (<= x5 x3)) (<= x6 x3)) x3 (ite (and (<= x5 x4) (<= x6 x4)) x4 (ite (<= x6 x5) x5 x6))))))
   ```

python3 ./programs/eu-like/main.py ./tests/open_tests/array_search_3.sl

   ```scheme
   (define-fun findIdx ((y1 Int) (y2 Int) (y3 Int) (k1 Int)) Int (ite (or (or (or (or (<= y2 y1) (<= y3 y2)) (<= k1 y1)) (= y3 k1)) (= y2 k1)) 0 (ite (<= k1 y2) 1 (ite (<= k1 y3) 2 3))))
   ```
