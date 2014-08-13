#lang racket
; The MIT License (MIT)
;
; Copyright (c) 2014 Andrew M. Kent
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in
; all copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
; THE SOFTWARE.
(require "main.rkt")

(struct test (assumptions conclusion expected))

(define (run-test t)
  (equal? (sli-proves-sli? (test-assumptions t)
                           (test-conclusion t))
          (test-expected t)))

; test1: 4 <= 3 is false
(define test1 (test empty
                    (list (leq (lexp (4 #f))
                               (lexp (3 #f))))
                    #f))



; test2: P and ~P --> false
(define test2 (test (list (leq (lexp) (lexp (1 'y)))
                          (leq-negate (leq (lexp) (lexp (1 'y)))))
                    (list (leq (lexp (4 #f))
                               (lexp (3 #f))))
                    #t))

; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
(define test3 (test (list (leq (lexp (1 'x) (1 'y))
                               (lexp (1 'z)))
                          (leq (lexp)
                               (lexp (1 'y)))
                          (leq (lexp)
                               (lexp (1 'x))))
                    (list (leq (lexp (1 'x))
                               (lexp (1 'z)))
                          (leq (lexp (1 'y))
                               (lexp (1 'z))))
                    #t))

; 7x <= 29 --> x <= 4
(define test4 (test (list (leq (lexp (7 'x))
                               (lexp (29 #f))))
                    (list (leq (lexp (1 'x))
                               (lexp (4 #f))))
                    #t))

; 7x <= 28 --> x <= 4
(define test5 (test (list (leq (lexp (7 'x))
                               (lexp (28 #f))))
                    (list (leq (lexp (1 'x))
                               (lexp (4 #f))))
                    #t))

; 7x <= 28 -/-> x <= 3
(define test6 (test (list (leq (lexp (7 'x))
                               (lexp (28 #f))))
                    (list (leq (lexp (1 'x))
                               (lexp (3 #f))))
                    #f))


; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
; x <= y + z; 
; 29r <= x + y + z + q; 
; 0 <= x;  
; 0 <= x + y + z; 
; 0 <= x + z; 
; x <= z
; z + 1 <= t
; 0 <= x + y;
; 0 <= x + r;
; 0 <= x + r + q;
; -->
; 0 <= t
(define test7 (test (list (leq (lexp (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
                               (lexp (4 'x) (3 'y) (9 'z) (20 'q) (100 'r)))
                          (leq (lexp (1 'x))
                               (lexp (1 'y) (1 'z)))
                          (leq (lexp (29 'r))
                               (lexp (1 'x) (1 'y) (1 'z) (1 'q)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'y) (1 'z)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'z)))
                          (leq (lexp (1 'x))
                               (lexp (1 'z)))
                          (leq (lexp (1 'z) (1 #f))
                               (lexp (1 't)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'y)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'r)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'r) (1 'q))))
                    (list (leq (lexp (0 #f))
                               (lexp (1 't))))
                    #t))

; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
; x <= y + z; 
; 29r <= x + y + z + q; 
; 0 <= x;  
; 0 <= x + y + z; 
; 0 <= x + z; 
; x <= z
; z + 1 <= t
; 0 <= x + y;
; 0 <= x + r;
; 0 <= x + r + q;
; -/->
; t <= 0
(define test8 (test (list (leq (lexp (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
                               (lexp (4 'x) (3 'y) (9 'z) (20 'q) (100 'r)))
                          (leq (lexp (1 'x))
                               (lexp (1 'y) (1 'z)))
                          (leq (lexp (29 'r))
                               (lexp (1 'x) (1 'y) (1 'z) (1 'q)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'y) (1 'z)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'z)))
                          (leq (lexp (1 'x))
                               (lexp (1 'z)))
                          (leq (lexp (1 'z) (1 #f))
                               (lexp (1 't)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'y)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'r)))
                          (leq (lexp (0 #f))
                               (lexp (1 'x) (1 'r) (1 'q))))
                    (list (leq (lexp (1 't))
                               (lexp (0 #f))))
                    #f))

(printf "test1 (4 <= 3 is false) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test1)))
(printf "\n")

(printf "test2 (P and (not P) --> false) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test2)))
(printf "\n")

(printf "test3 (x + y <= z; 0 <= y; 0 <= x --> x <= z /\\ y <= z) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test3)))
(printf "\n")

(printf "test4 (7x <= 29 --> x <= 4) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test4)))
(printf "\n")

(printf "test5 (7x <= 28 --> x <= 4) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test5)))
(printf "\n")

(printf "test6 (7x <= 28 -/-> x <= 3) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test6)))
(printf "\n")

(printf "test7 (large valid) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test7)))
(printf "\n")

(printf "test8 (large invalid) x 100,000...\n")
(time (for ([i (range 100000)])
        (run-test test8)))