#lang racket/base

;; *****************************************************************************
;; leq.rkt
;; linear inequalities (e.g. ax_1 + bx_2 ... <= cy_1 + dy_2 + ...) and
;; related ops.
;; 
;; Inequalities are kept in a normal form, reduced by their greatest gcd
;; (e.g. 4x + 8y <= 12z + 16 would be normalized to x + 2y <= 3z + 4since
;; 4 is the gcd of the scalars in the inequalities).
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

(require "fme-utils.rkt" "lexp.rkt"
         racket/contract
         racket/match
         racket/format)

(provide (except-out (all-defined-out)
                     leq
                     make-leq
                     leq*)
         (rename-out [leq* leq]))

(define-struct/cond-contract leq
  ([lhs lexp?] [rhs lexp?])
  #:transparent)

;; smart constructor for leqs
;; divides both side by gcd of scalars
;; if necc.
(define/cond-contract (leq* l1 l2)
  (-> lexp? lexp? leq?)
  (let ([gcd* (apply gcd (append (lexp-scalars l1)
                                 (lexp-scalars l2)))])
    (cond
      [(<= gcd* 1) (leq l1 l2)]
      [else (leq (lexp-scale l1 (/ gcd*))
                 (lexp-scale l2 (/ gcd*)))])))

; leq-exps
(define/cond-contract (leq-lexps ineq)
  (-> leq? (values lexp? lexp?))
  (values (leq-lhs ineq) (leq-rhs ineq)))


; leq-contains-var
(define/cond-contract (leq-contains-var? ineq x)
  (-> leq? any/c boolean?)
  (or (lexp-has-var? (leq-lhs ineq) x)
      (lexp-has-var? (leq-rhs ineq) x)))

; leq-vars
(define/cond-contract (leq-vars ineq)
  (-> leq? list?)
  (let-values ([(l r) (leq-lexps ineq)])
    (union (lexp-vars l)
           (lexp-vars r))))

; leq-negate
; ~ (l1 <= l2) ->
; l2 <= 1 + l1 
; (obviously this is valid for integers only)
(define/cond-contract (leq-negate ineq)
  (-> leq? leq?)
  (let-values ([(l r) (leq-lexps ineq)])
    (leq* (lexp-add1 r) l)))

(module+ test
  (require rackunit)
  
  (check-equal? (leq-negate (leq* (lexp 0 '(1 x))
                                  (lexp 0 '(1 y))))
                (leq* (lexp 1 '(1 y))
                      (lexp 0 '(1 x)))))
;; leq-isolate-var
;; converts leq with x into either:
;;  1) ax <= by + cz + ...
;;  or
;;  2) by + cz + ... <= ax
;;  where a is a positive integer and x is on at most 
;;  one side of the inequality
(define/cond-contract (leq-isolate-var ineq x)
  (-> leq? any/c leq?)
  ;; ... + ax + .... <= ... + bx + ...
  (let*-values ([(l r) (leq-lexps ineq)]
                [(a) (lexp-coeff l x)]
                [(b) (lexp-coeff r x)])
    (cond
      [(= a b)
       (leq* (lexp-set l x 0)
             (lexp-set r x 0))]
      [(< a b)
       (leq* (lexp-set (lexp-minus l r) x 0)
             (lexp (list (- b a) x)))]
      [else
       (leq* (lexp (list (- a b) x))
             (lexp-set (lexp-minus r l) x 0))])))

; x lhs
(module+ test
  (check-equal? (leq-isolate-var (leq* (lexp '(3 x) '(2 z) '(5 y))
                                       (lexp '(1 x) '(1 z)))
                                 'x)
                (leq* (lexp '(2 x)) (lexp '(-5 y) '(-1 z))))
  
  ;; x rhs
  (check-equal? (leq-isolate-var (leq* (lexp '(3 x) '(2 z) '(5 y))
                                       (lexp '(1 z) '(33 x)))
                                 'x)
                (leq* (lexp '(1 z) '(5 y)) (lexp '(30 x))))
  ;; x eq
  (check-equal? (leq-isolate-var (leq* (lexp '(42 x) '(2 z) '(5 y))
                                       (lexp '(42 x) '(1 z)))
                                 'x)
                (leq* (lexp '(2 z) '(5 y))
                      (lexp '(1 z))))
  ;; no x
  (check-equal? (leq-isolate-var (leq* (lexp '(2 z) '(5 y))
                                       (lexp '(1 z)))
                                 'x)
                (leq* (lexp '(2 z) '(5 y))
                      (lexp '(1 z))))
  
  ; x mix
  (check-equal? (leq-isolate-var (leq* (lexp '(2 x) '(4 y) 1)
                                       (lexp '(2 y))) 'x)
                (leq* (lexp '(2 x))
                      (lexp '-1 '(-2 y)))))


;; leq-join
;; takes a pair a1x <= l1 and l2 <= a2x
;; and returns a2l1 <= a1l2
(define/cond-contract (leq-join leq1 leq2 x)
  (-> leq? leq? any/c leq?)
  ;; leq1: ... + ax + .... <= ... + bx + ...
  ;; leq2: ... + cx + .... <= ... + dx + ...
  (let*-values ([(l1 r1) (leq-lexps leq1)]
                [(l2 r2) (leq-lexps leq2)])
    (match* ((lexp-coeff l1 x) (lexp-coeff r1 x) 
             (lexp-coeff l2 x) (lexp-coeff r2 x))
      ; leq1: ax <= l1
      ; leq2: l2 <= dx
      [(a 0
        0 d)
       (leq* (lexp-scale l2 a)
             (lexp-scale r1 d))]
      ; leq1: l1 <= bx
      ; leq2: cx <= l2
      [(0 b 
        c 0)
       (leq* (lexp-scale l1 c)
             (lexp-scale r2 b))]
      [(_ _ _ _) (error 'leq-join "cannot join ~a and ~a by ~a" leq1 leq2 x)])))

(module+ test 
  (check-equal? (leq-join (leq* (lexp '(2 x))
                               (lexp '(4 y) 10))
                          (leq* (lexp '(4 z) 2)
                               (lexp '(4 x)))
                          'x)
                (leq* (lexp '(2 z) 1)
                     (lexp '(4 y) 10))))


;; trivially-valid?
(define/cond-contract (leq-trivially-valid? ineq)
  (-> leq? boolean?)
  (let-values ([(l r) (leq-lexps ineq)])
      (or (and (constant-lexp? l)
               (constant-lexp? r)
               (<= (lexp-const l) (lexp-const r)))
          (equal? l r))))


;; leq-subst
;(define/contract (leq-subst ineq new old)
;  (-> leq? any/c any/c leq?)
;  (leq* (lexp-subst (leq-lhs ineq) new old)
;       (lexp-subst (leq-rhs ineq) new old)))
;
;(module+ test
;  (check-equal? (leq-subst (leq-subst (leq* (list->lexp '(1 x))
;                                           (list->lexp '(1 y)))
;                                      'y2 
;                                      'y)
;                           'x2
;                           'x)
;                (leq* (list->lexp '(1 x2))
;                     (list->lexp '(1 y2)))))
;
;
;#|
;; leq-subst
;(define/contract (leq-subst-list->lexp ineq new-list->lexp old-var)
;  (-> leq? lexp? any/c leq?)
;  (leq* (lexp-subst-list->lexp (leq-lhs ineq) new-list->lexp old-var)
;       (lexp-subst-list->lexp (leq-rhs ineq) new-list->lexp old-var)))
;|#
(define/cond-contract (leq->string ineq [pp #f])
  (-> leq? (-> any/c any/c) string?)
  (define-values (lhs rhs) (leq-lexps ineq))
  (string-append (lexp->string lhs pp) " ≤ " (lexp->string rhs pp)))

