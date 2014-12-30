#lang racket/base

;; *****************************************************************************
;; fme.rkt
;; Fourier-Motzkin elimination implementation
;; http://en.wikipedia.org/wiki/Fourier-Motzkin_elimination
;;
;; Uses non-matrix representations of data (racket sets, so as to avoid
;; duplicate inequalities)
;; *****************************************************************************

;; The MIT License (MIT)
;;
;; Copyright (c) 2014 Andrew M. Kent
;;
;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
;; THE SOFTWARE.


(require "fme-utils.rkt" 
         "lexp.rkt" 
         "leq.rkt"
         racket/contract
         racket/set
         racket/function)

(provide (except-out (all-defined-out)
                     cartesian-map))

(define (sli? s) 
  (and (set? s)
       (for/and ([l (in-set s)])
         (leq? l))))

(define/cond-contract (sli->string sli)
  (-> sli? string?)
  (string-append 
   (cond
     [(set-empty? sli) "("]
     [else
      (for/fold ([str (leq->string (set-first sli))])
                ([ineq (set-rest sli)])
        (string-append str " ∧ "(leq->string ineq)))])
   ")"))


; sli-vars
(define/cond-contract (sli-vars sli)
  (-> sli? list?)
  (for/fold ([vars '()])
            ([l (in-set sli)])
    (union (leq-vars l)
           vars)))

(module+ test
  (require rackunit)
  
  (check-equal? (list->set (sli-vars (set (leq (lexp '(1 x))
                                               (lexp '(1 y)))
                                          (leq (lexp '(1 x) '(1 z))
                                               (lexp '(1 q)))
                                          (leq (lexp '(1 r) '(3 z))
                                               (lexp '(1 x))))))
                (list->set '(r q z y x)))
  (check-equal? (length (sli-vars (set (leq (lexp '(1 x))
                                            (lexp '(1 y)))
                                       (leq (lexp '(1 x) '(1 z))
                                            (lexp '(1 q)))
                                       (leq (lexp '(1 r) '(3 z))
                                            (lexp '(1 x))))))
                5))

;; sli-subst
;(define/cond-contract (sli-subst sli new old)
;  (-> (listof leq?) any/c any/c (listof leq?))
;  (map (λ (x) (leq-subst x new old)) sli))

;; sli-subst-lexp
;(define/contract (sli-subst-lexp sli new-lexp old-var)
;  (-> (listof Leq?) lexp? any/c (listof Leq?))
;  (map (λ (x) (leq-subst-lexp x new-lexp old-var)) sli))
;
;; sli-partition
;; partitions leq expressions into
;; 3 lists of x-normalized inequalities:
;;  value 1) set of (ax <= by + cz + ...) leqs
;;  value 2) set of form (by + cz + ... <= ax) leqs
;;  value 3) leqs w/o x
(define/cond-contract (sli-partition leqs x)
  (-> sli? any/c (values sli? sli? sli?))
  (define leqs* (for/set ([ineq (in-set leqs)])
                  (leq-isolate-var ineq x)))
  (for/fold ([xlhs (set)]
             [xrhs (set)]
             [nox (set)]) 
            ([ineq (in-set leqs*)])
    (cond
      [(lexp-has-var? (leq-lhs ineq) x)
       (values (set-add xlhs ineq) xrhs nox)]
      [(lexp-has-var? (leq-rhs ineq) x)
       (values xlhs (set-add xrhs ineq) nox)]
      [else
       (values xlhs xrhs (set-add nox ineq))])))

(module+ test
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp '(2 x) '(4 y) 1)
                                                       (lexp '(2 y)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp '(2 x)) 
                                (lexp '(-2 y) -1)))
                      (set)
                      (set)))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp '(2 x) '(4 y) 1)
                                                       (lexp '(2 y)))
                                                  (leq (lexp '(2 x) '(4 y))
                                                       (lexp '(2 y) '(42 x)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp '(2 x)) 
                                 (lexp '(-2 y) -1)))
                      (set (leq (lexp '(2 y))
                                 (lexp '(40 x))))
                      (set)))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition (set (leq (lexp '(2 x) '(4 y) -1)
                                                       (lexp '(2 y)))
                                                  (leq (lexp '(2 x) '(4 y))
                                                       (lexp '(2 y) '(42 x)))
                                                  (leq (lexp '(2 z) '(4 y))
                                                       (lexp '(2 y) '(42 q)))) 
                                             'x)])
                  (list lt gt no))
                (list (set (leq (lexp '(2 x)) 
                                (lexp '(-2 y) 1)))
                      (set (leq (lexp '(2 y))
                                (lexp '(40 x))))
                      (set (leq (lexp '(2 z) '(4 y))
                                (lexp '(2 y) '(42 q)))))))


;; cartesian-map
;; map of f over each pair of cartesian
;; product of input lists
;; order not guaranteed
(define/cond-contract (cartesian-map f xs ys)
  (-> procedure? set? set? set?)
  (for*/fold ([result (set)]) 
             ([x (in-set xs)] 
              [y (in-set ys)])
    (set-add result (f x y))))


;; eliminate-var
;; reduces the system of linear inequalties,
;; removing x
(define/cond-contract (fme-elim sli x)
  (-> sli? any/c sli?)
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (set-union (cartesian-map (curryr leq-join x) 
                            xltleqs
                            xgtleqs)
             noxleqs))

;; reduces the system of linear inequalties,
;; removing variables x for which (pred? x) = #t
(define/cond-contract (fme-elim* sli pred?)
  (-> sli? any/c sli?)
  (define vars (filter pred? (sli-vars sli)))
  (for/fold ([s sli]) 
            ([x (in-list vars)])
    (fme-elim s x)))

;; sli-satisfiable?
(define/cond-contract (fme-sat? sli)
  (-> sli? boolean?)
  (let* ([vars (sli-vars sli)]
         [simple-system (for/fold ([s sli]) 
                                  ([x (in-list vars)])
                          (fme-elim s x))])
    (for/and ([ineq (in-set simple-system)])
      (leq-trivially-valid? ineq))))


(module+ test
  ; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
  (check-true (fme-sat? (set (leq (lexp '(3 x) '(2 y))
                                  (lexp 7))
                             (leq (lexp '(6 x) '(4 y))
                                  (lexp 15))
                             (leq (lexp '(-1 x))
                                  (lexp 1))
                             (leq (lexp 0)
                                  (lexp '(2 y))))))
  
  ; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
  (check-false (fme-sat? (set (leq (lexp '(3 x) '(2 y))
                                   (lexp 4))
                              (leq (lexp 1)
                                   (lexp '(1 x)))
                              (leq (lexp 1)
                                   (lexp '(1 y)))))))

;;**********************************************************************
;; Logical Implication for Integer Linear Inequalities
;; using Fourier-Motzkin elimination
;;**********************************************************************

(define/cond-contract (fme-imp-leq? s ineq)
  (-> sli? leq? boolean?)
  (not (fme-sat? (set-add s (leq-negate ineq)))))

(module+ test
  ; transitivity! x <= y /\ y <= z --> x <= z
  (check-true (fme-imp-leq? (set (leq (lexp '(1 x))
                                      (lexp '(1 y)))
                                 (leq (lexp '(1 y))
                                      (lexp '(1 z))))
                            (leq (lexp '(1 x))
                                 (lexp '(1 z)))))


  ; x  <= x;
  (check-true (fme-imp-leq? (set)
                            (leq (lexp '(1 x))
                                 (lexp '(1 x)))))
  
  ; x  - 1 <= x + 1;
  (check-true (fme-imp-leq? (set)
                            (leq (lexp '(1 x) -1)
                                 (lexp '(1 x) 1))))
  
  
  ; x + y <= z; 1 <= y; 0 <= x --> x + 1 <= z
  (check-true (fme-imp-leq? (set (leq (lexp '(1 x) '(1 y))
                                      (lexp '(1 z)))
                                 (leq (lexp 1)
                                      (lexp '(1 y)))
                                 (leq (lexp)
                                      (lexp '(1 x))))
                            (leq (lexp '(1 x) 1)
                                 (lexp '(1 z))))))

;;**********************************************************************
;; Logical Implication for Systems of Integer Linear Inequalities
;; using Fourier-Motzkin elimination
;;**********************************************************************

(define/cond-contract (fme-imp? axioms goals)
  (-> sli? sli? boolean?)
  (for/and ([ineq (in-set goals)])
    (fme-imp-leq? axioms ineq)))


(module+ test
  ;; 4 <= 3 is false
  (check-false (fme-imp? (set)
                         (set (leq (lexp 4)
                                   (lexp 3)))))
  ;; P and ~P --> false
  (check-true (fme-imp? (set (leq (lexp) (lexp '(1 y)))
                             (leq-negate (leq (lexp) (lexp '(1 y)))))
                        (set (leq (lexp 4)
                                  (lexp 3)))))
  
  
  ;; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
  (check-true (fme-imp? (set (leq (lexp '(1 x) '(1 y))
                                  (lexp '(1 z)))
                             (leq (lexp)
                                  (lexp '(1 y)))
                             (leq (lexp)
                                  (lexp '(1 x))))
                        (set (leq (lexp '(1 x))
                                  (lexp '(1 z)))
                             (leq (lexp '(1 y))
                                  (lexp '(1 z))))))
  
  ;; x + y <= z; 0 <= y; 0 <= x -/-> x <= z /\ y <= q
  (check-false (fme-imp? (set (leq (lexp '(1 x) '(1 y))
                                   (lexp '(1 z)))
                              (leq (lexp)
                                   (lexp '(1 y)))
                              (leq (lexp)
                                   (lexp '(1 x))))
                         (set (leq (lexp '(1 x))
                                   (lexp '(1 z)))
                              (leq (lexp '(1 y))
                                   (lexp '(1 q))))))
  
  ;; 7x <= 29 --> x <= 4
  (check-true (fme-imp? (set (leq (lexp '(7 x))
                                  (lexp 29)))
                        (set (leq (lexp '(1 x))
                                  (lexp 4)))))
  ;; 7x <= 28 --> x <= 4
  (check-true (fme-imp? (set (leq (lexp '(7 x))
                                  (lexp 28)))
                        (set (leq (lexp '(1 x))
                                  (lexp 4)))))
  ;; 7x <= 28 does not --> x <= 3
  (check-false (fme-imp? (set (leq (lexp '(7 x))
                                   (lexp 28)))
                         (set (leq (lexp '(1 x))
                                   (lexp 3)))))
  
  
  ;; 7x <= 27 --> x <= 3
  (check-true (fme-imp? (set (leq (lexp '(7 x))
                                  (lexp 27)))
                        (set (leq (lexp '(1 x))
                                  (lexp 3)))))
  
  ;; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
  ;; x <= y + z; 
  ;; 29r <= x + y + z + q; 
  ;; 0 <= x;  
  ;; 0 <= x + y + z; 
  ;; 0 <= x + z; 
  ;; x <= z
  ;; z + 1 <= t
  ;; 0 <= x + y;
  ;; 0 <= x + r;
  ;; 0 <= x + r + q;
  ;; -->
  ;; 0 <= t
  (check-true (fme-imp? (set (leq (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                  (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                             (leq (lexp '(1 x))
                                  (lexp '(1 y) '(1 z)))
                             (leq (lexp '(29 r))
                                  (lexp '(1 x) '(1 y) '(1 z) '(1 q)))
                             (leq (lexp)
                                  (lexp '(1 x)))
                             (leq (lexp)
                                  (lexp '(1 x) '(1 y) '(1 z)))
                             (leq (lexp)
                                  (lexp '(1 x) '(1 z)))
                             (leq (lexp '(1 x))
                                  (lexp '(1 z)))
                             (leq (lexp '(1 z) 1)
                                  (lexp '(1 t)))
                             (leq (lexp)
                                  (lexp '(1 x) '(1 y)))
                             (leq (lexp)
                                  (lexp '(1 x) '(1 r)))
                             (leq (lexp)
                                  (lexp '(1 x) '(1 r) '(1 q))))
                        (set (leq (lexp)
                                  (lexp '(1 t))))))
  
  ;; 4x+3y+9z+20q-100r + 42 <= 4x+3y+9z+20q+100r; 
  ;; x <= y + z; 
  ;; 29r <= x + y + z + q; 
  ;; 0 <= x;  
  ;; 0 <= x + y + z; 
  ;; 0 <= x + z; 
  ;; x <= z
  ;; z + 1 <= t
  ;; 0 <= x + y;
  ;; 0 <= x + r;
  ;; 0 <= x + r + q;
  ;; -/->
  ;; t <= 0
  (check-false (fme-imp? (set (leq (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                   (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                              (leq (lexp '(1 x))
                                   (lexp '(1 y) '(1 z)))
                              (leq (lexp '(29 r))
                                   (lexp '(1 x) '(1 y) '(1 z) '(1 q)))
                              (leq (lexp)
                                   (lexp '(1 x)))
                              (leq (lexp)
                                   (lexp '(1 x) '(1 y) '(1 z)))
                              (leq (lexp)
                                   (lexp '(1 x) '(1 z)))
                              (leq (lexp '(1 x))
                                   (lexp '(1 z)))
                              (leq (lexp '(1 z) 1)
                                   (lexp '(1 t)))
                              (leq (lexp)
                                   (lexp '(1 x) '(1 y)))
                              (leq (lexp)
                                   (lexp '(1 x) '(1 r)))
                              (leq (lexp)
                                   (lexp '(1 x) '(1 r) '(1 q))))
                         (set (leq (lexp '(1 t))
                                   (lexp))))))