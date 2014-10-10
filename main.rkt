#lang racket/base
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


;**********************************************************************
; Integer Inequality Proving Library
;**********************************************************************
;
; This library aims to provide a sound algorithm for deciding
; if one system of linear inequalities over integers (P) implies
; another (Q) by assuming (P /\ ~Q) and testing for unsatisfiability.
;
; The transformations are based on the fourier-motzkin elimination method.
; Variables are eliminated until the system is trivial.
;
; Elimination is performed as follows:
;   1) partition the set of inequalities into those which can be 
;      written as a*x <= l, those which can be written as l <= a*x,
;      and those without x (where a is a positive coefficient and l
;      is a linear combination of variables and coefficients)
;   2) for each possible pairing l1 <= a1*x  and a2*x <= l2, we add
;      a2*l1 <= a1*l2 to the system and remove the equations with x
;      - now our system is larger and does not contain the variable x
;   3) this is repeated until the system can be trivially checked
;      to see if it is unsatisfiable
;
; Because this method is for linear inequalities with variables that range
; over reals (and not integers), it is a sound but incomplete model with 
; respect to testing for unsatisfiability
;
; All inequalities in this system are represented with <=
; For negation we utilize the equivalence ~(a <= b) <-> 1 + b <= a
; since we are concerned with integer solutions.

(require racket/list racket/bool racket/contract racket/match)
(module+ test
    (require rackunit))
(provide (all-defined-out))

;**********************************************************************
; Linear Expression  (lexp)
; ax + by + cz + ...
;   (and related operations)
;**********************************************************************

; defining linear combinations
; takes list of (scalar symbol)
; #f is used for a constant
(struct constant () #:transparent)
(define CONST (constant))
(define lexp? hash?)

(define/contract (lexp . terms)
  (->* () #:rest (listof (or/c integer? (list/c integer? any/c))) lexp?)
  (define coef first) 
  (define var second)
  (let loop ([h (hash)]
             [zxs terms])
    (match zxs
      ['() h]
      [(cons (? integer? z) zxs-rest)
       (if (zero? z)
           (loop h zxs-rest)
           (loop (hash-set h CONST (+ (hash-ref h CONST 0) z)) zxs-rest))]
      [(cons (list z x) zxs-rest)
       (if (zero? z)
           (loop h zxs-rest)
           (loop (hash-set h x (+ (hash-ref h x 0) z)) zxs-rest))])))

; lexp-scalar
(define/contract (lexp-scalar exp var)
  (-> lexp? any/c integer?)
  (hash-ref exp var 0))

;; lexp-equal?
(define/contract (lexp-equal? l1 l2)
  (-> lexp? lexp? boolean?)
  (for/and ([key (hash-keys l1)])
    (= (lexp-scalar l1 key)
       (lexp-scalar l2 key))))

(module+ test
  (check-equal? (lexp 0) (lexp 0 '(0 x) '(0 y) '(0 z)))
  
  (check-equal? (lexp-scalar (lexp 1 '(1 x) '(42 y)) 'y) 42)
  (check-equal? (lexp-scalar (lexp 1 '(1 x) '(42 y)) CONST) 1)
  (check-equal? (lexp-scalar (lexp 0 '(1 x) '(42 y)) 'q) 0))


(define/contract (lexp-vars exp)
  (-> lexp? list?)
  (hash-keys exp))

(module+ test
  (check-not-false (let ([vars (lexp-vars (lexp 17 '(42 x)))])
                     (and (= 2 (length vars))
                          (member 'x vars)
                          (member CONST vars)))))

; lexp-scale
(define/contract (lexp-scale exp a)
  (-> lexp? integer? lexp?)
  (for/hash ([x (lexp-vars exp)])
    (values x (* a (lexp-scalar exp x)))))

(module+ test
  (check-equal? (lexp-set (lexp 17 '(42 x)) 'x 0)
                (lexp 17)))

; lexp-set
; excludes items set to 0
(define/contract (lexp-set exp var scalar)
  (-> lexp? any/c integer? lexp?)
  (if (zero? scalar)
      (hash-remove exp var)
      (hash-set exp var scalar)))

(module+ test 
  (check-true (lexp-equal? (lexp-set (lexp 17) 'x 42)
                           (lexp 17 '(42 x))))
  (check-true (lexp-equal? (lexp-set (lexp 17 '(2 x)) 'x 42)
                           (lexp 17 '(42 x)))))

; lexp-empty?
(define/contract (lexp-zero? exp)
  (-> lexp? boolean?)
  (lexp-equal? exp
               (lexp 0)))

(module+ test
  (check-false (lexp-zero? (lexp 17 '(42 x))))
  (check-false (lexp-zero? (lexp 17)))
  (check-not-false (lexp-zero? (lexp 0))))

; lexp-subtract
(define/contract (lexp-subtract exp1 exp2)
  (-> lexp? lexp? lexp?)
  (define vars (lexp-vars exp2))
    (for/fold ([exp exp1]) ([x vars])
    (let* ([s1 (lexp-scalar exp1 x)]
           [s2 (lexp-scalar exp2 x)]
           [snew (- s1 s2)])
      (lexp-set exp x snew))))

(module+ test
  (check-true (lexp-equal? (lexp-subtract (lexp -1 '(2 x) '(3 y))
                                          (lexp -1 '(2 x) '(42 z)))
                           (lexp 0 '(3 y) '(-42 z))))
  (check-true (lexp-equal? (lexp-subtract (lexp 0)
                                         (lexp -1 '(2 x) '(42 z)))
                           (lexp 1 '(-2 x) '(-42 z)))))

; lexp-has-var?
(define/contract (lexp-has-var? exp x)
  (-> lexp? any/c boolean?)
  (not (zero? (lexp-scalar exp x))))

(module+ test
  (check-false (lexp-has-var? (lexp 17 '(42 x)) 'y))
  (check-not-false (lexp-has-var? (lexp 17 '(42 x)) 'x)))

; lexp-add1
(define (lexp-add1 exp)
  (-> lexp? lexp?)
  (lexp-set exp CONST (add1 (lexp-scalar exp CONST))))

(module+ test 
  (check-equal? (lexp-add1 (lexp 0)) (lexp 1))
  (check-true (lexp-equal? (lexp-add1 (lexp 1 '(5 x))) 
                           (lexp 2 '(5 x)))))

; lexp-subst
(define (lexp-subst exp new old)
  (-> lexp? any/c any/c lexp?)
  (if (lexp-has-var? exp old)
      (lexp-set (lexp-set exp old 0) new (lexp-scalar exp old))
      exp))

(module+ test
  (check-true (lexp-equal? (lexp-subst (lexp 1 '(5 x) '(42 z)) 'y 'x) 
                             (lexp 1 '(5 y) '(42 z)))))


;**********************************************************************
; Linear Inequalities  (leq)
; a1x1 + a1x2 + ... <= b1y1 + b2y2 + ...
;   (and related operations)
;**********************************************************************

; leq def
(struct leq (lhs rhs) #:transparent
  #:guard (λ (l r name)
            (unless (and (lexp? l)
                         (lexp? r))
              (error "invalid linear inequality"))
            (values l r)))

; leq-exps
(define/contract (leq-exps ineq)
  (-> leq? (values lexp? lexp?))
  (values (leq-lhs ineq) (leq-rhs ineq)))

;; leq-equal?
(define/contract (leq-equal? l1 l2)
  (-> leq? leq? boolean?)
  (define-values (l1lhs l1rhs) (leq-exps l1))
  (define-values (l2lhs l2rhs) (leq-exps l2))
  (and (lexp-equal? l1lhs l2lhs)
       (lexp-equal? l1rhs l2rhs)))


; leq-contains-var
(define/contract (leq-contains-var? ineq var)
  (-> leq? any/c boolean?)
  (or (lexp-has-var? (leq-lhs ineq) var)
      (lexp-has-var? (leq-rhs ineq) var)))

(define (union l1 l2)
  (cond
    [(empty? l1) l2]
    [(member (first l1) l2)
     (union (rest l1) l2)]
    [else
     (union (rest l1) (cons (first l1) l2))]))

; leq-vars
(define/contract (leq-vars ineq)
  (-> leq? list?)
  (union (lexp-vars (leq-lhs ineq))
         (lexp-vars (leq-rhs ineq))))

; leq-negate
; ~ (l1 <= l2) ->
; l2 <= 1 + l1 
; (obviously this is valid for integers only)
(define (leq-negate ineq)
  (-> leq? leq?)
  (leq (lexp-add1 (leq-rhs ineq))
       (leq-lhs ineq)))

(module+ test
  (check-true (leq-equal? (leq-negate (leq (lexp 0 '(1 x))
                                            (lexp 0 '(1 y))))
                           (leq (lexp 1 '(1 y))
                                (lexp 0 '(1 x))))))
; leq-isolate-var
; converts leq with x into either:
;  1) ax <= by + cz + ...
;  or
;  2) by + cz + ... <= ax
;  where a is a positive integer and x is on at most 
;  one side of the inequality
(define (leq-isolate-var ineq x)
  (-> leq? any/c)
  (define-values (lhs rhs) (leq-exps ineq))
  ; ... + ax + .... <= ... + bx + ...
  (define a (lexp-scalar lhs x))
  (define b (lexp-scalar rhs x))
  (cond
    [(and a b (= a b))
     (leq (lexp-set lhs x 0)
          (lexp-set rhs x 0))]
    [(and a b (< a b))
     (leq (lexp-set (lexp-subtract lhs rhs) x 0)
          (lexp `(,(- b a) ,x)))]
    [(and a b (> a b))
     (leq (lexp `(,(- a b) ,x))
          (lexp-subtract (lexp-set rhs x 0)
                         (lexp-set lhs x 0)))]
    [else
     ineq]))

; x lhs
(module+ test
  (check-equal? (leq-isolate-var (leq (lexp '(3 x) '(2 z) '(5 y))
                                      (lexp '(1 x) '(1 z)))
                                 'x)
                (leq (lexp '(2 x)) (lexp '(-5 y) '(-1 z))))
  
  ;; x rhs
  (check-equal? (leq-isolate-var (leq (lexp '(3 x) '(2 z) '(5 y))
                                      (lexp '(1 z) '(33 x)))
                                 'x)
                (leq (lexp '(1 z) '(5 y)) (lexp '(30 x))))
  ;; x eq
  (check-equal? (leq-isolate-var (leq (lexp '(42 x) '(2 z) '(5 y))
                                      (lexp '(42 x) '(1 z)))
                                 'x)
                (leq (lexp '(2 z) '(5 y))
                     (lexp '(1 z))))
  ;; no x
  (check-equal? (leq-isolate-var (leq (lexp '(2 z) '(5 y))
                                      (lexp '(1 z)))
                                 'x)
                (leq (lexp '(2 z) '(5 y))
                     (lexp '(1 z))))

                                        ; x mix
  (check-equal? (leq-isolate-var (leq (lexp '(2 x) '(4 y) 1)
                                      (lexp '(2 y))) 'x)
                (leq (lexp '(2 x))
                     (lexp -1 '(-2 y)))))

;; BOOKMARK

; leq-join
; takes a pair a1x <= l1 and l2 <= a2x
; and returns a2l1 <= a1l2
(define (leq-join leq1 leq2 x)
  (define-values (lhs1 rhs1) (leq-exps leq1))
  (define-values (lhs2 rhs2) (leq-exps leq2))
  (cond
    ; leq1: a1x <= l1
    ; leq2: l2 <= a2x
    [(and (lexp-scalar lhs1 x) (not (lexp-scalar rhs1 x #f))
          (lexp-scalar rhs2 x) (not (lexp-scalar lhs2 x #f)))
     (let ([a1 (lexp-scalar lhs1 x)]
           [a2 (lexp-scalar rhs2 x)])
       (leq (lexp-scale lhs2 a1)
            (lexp-scale rhs1 a2)))]
    ; leq1: l1 <= a1x
    ; leq2: a2x <= l2
    [(and (lexp-scalar rhs1 x) (not (lexp-scalar lhs1 x #f))
          (lexp-scalar lhs2 x) (not (lexp-scalar rhs2 x #f)))
     (let ([a1 (lexp-scalar rhs1 x)]
           [a2 (lexp-scalar lhs2 x)])
       (leq (lexp-scale lhs1 a2)
            (lexp-scale rhs2 a1)))]
    [else
     (error "bad pair for joining by ~a: ~a, ~a" x leq1 leq2)]))

(module+ test 
  (check-equal? (leq-join (leq (lexp (2 'x))
                               (lexp (4 'y) (10 #f)))
                          (leq (lexp (4 'z) (2 #f))
                               (lexp (4 'x)))
                          'x)
                (leq (lexp (8 'z) (4 #f))
                     (lexp (16 'y) (40 #f)))))


; trivially-valid?
(define (leq-trivially-valid? ineq)
  (unless (or (empty? (leq-vars ineq))
              (equal? (list #f) (leq-vars ineq)))
    (error 'trivially-valid? "non-trivial inequality: ~a" ineq))
  (define lhs-val (lexp-scalar (leq-lhs ineq) #f 0))
  (define rhs-val (lexp-scalar (leq-rhs ineq) #f 0))
  (<= lhs-val rhs-val))


; leq-subst
(define (leq-subst ineq new old)
  (leq (lexp-subst (leq-lhs ineq) new old)
       (lexp-subst (leq-rhs ineq) new old)))

(module+ test
  (check-equal? (leq-subst (leq-subst (leq (lexp (1 'x))
                                           (lexp (1 'y)))
                                      'y2 
                                      'y)
                           'x2
                           'x)
                (leq (lexp (1 'x2))
                     (lexp (1 'y2)))))

;**********************************************************************
; Systems of Integer Linear Inequalities (sli)
; a1x1 + a2x2 + ... <= b1y1 + b2y2 + ...
; c1z1 + c2z2 + ... <= d1q1 + d2q2 + ...
; ...
;   (and related operations)
;**********************************************************************

(define sli list)
(define empty-sli empty)

; sli-vars
(define (sli-vars sli)
  (remove-duplicates (apply append (map leq-vars sli))))

; sli-subst
(define (sli-subst sli new old)
  (map (λ (x) (leq-subst x new old)) sli))

; sli-partition
; partitions leq expressions into
; 3 lists of x-normalized inequalities:
;  value 1) list of (ax <= by + cz + ...) leqs
;  value 2) list of form (by + cz + ... <= ax) leqs
;  value 3) leqs w/o x
(define (sli-partition leqs x)
  (define nleqs (map (λ (ineq) (leq-isolate-var ineq x)) leqs))
  (for/fold ([xslhs empty]
             [xsrhs empty]
             [noxs empty]) ([ineq nleqs])
    (cond
      [(lexp-has-var? (leq-lhs ineq) x)
       (values (cons ineq xslhs) xsrhs noxs)]
      [(lexp-has-var? (leq-rhs ineq) x)
       (values xslhs (cons ineq xsrhs) noxs)]
      [else
       (values xslhs xsrhs (cons ineq noxs))])))

(module+ test
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (sli (leq (lexp (2 'x) (4 'y) (1 #f))
                                                        (lexp (2 'y)))) 
                                              'x)])
                  (list lt gt no))
                (list (list (leq (lexp (2 'x)) 
                                 (lexp (-2 'y) (-1 #f))))
                      empty
                      empty))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (sli (leq (lexp (2 'x) (4 'y) (1 #f))
                                                        (lexp (2 'y)))
                                                   (leq (lexp (2 'x) (4 'y))
                                                        (lexp (2 'y) (42 'x)))) 
                                              'x)])
                  (list lt gt no))
                (list (list (leq (lexp (2 'x)) 
                                 (lexp (-2 'y) (-1 #f))))
                      (list (leq (lexp (2 'y))
                                 (lexp (40 'x))))
                      empty))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (sli (leq (lexp (2 'x) (4 'y) (-1 #f))
                                                        (lexp (2 'y)))
                                                   (leq (lexp (2 'x) (4 'y))
                                                        (lexp (2 'y) (42 'x)))
                                                   (leq (lexp (2 'z) (4 'y))
                                                        (lexp (2 'y) (42 'q)))) 
                                              'x)])
                  (list lt gt no))
                (list (sli (leq (lexp (2 'x)) 
                                (lexp (-2 'y) (1 #f))))
                      (sli (leq (lexp (2 'y))
                                (lexp (40 'x))))
                      (sli (leq (lexp (2 'z) (4 'y))
                                (lexp (2 'y) (42 'q)))))))


; cartesian-map
; map of f over each pair of cartesian
; product of input lists
; order not guaranteed
(define (cartesian-map f xs ys)
  (for*/fold ([result empty]) ([x xs] [y ys])
    (cons (f x y) result)))


; eliminate-var
; reduces the system of linear inequalties,
; removing x
(define (sli-elim-var sli x)
  (unless (and x (list? sli))
    (error 'sli-elim-var "can't eliminate constant scalars from ineqs"))
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (append (cartesian-map (λ (leq1 leq2) (leq-join leq1 leq2 x)) 
                         xltleqs 
                         xgtleqs)
          noxleqs))

; sli-satisfiable?
(define (sli-satisfiable? sli)
  (unless (and (list? sli) (not (empty? sli)))
    (error 'sli-satisfiable? "invalid sli: ~a" sli))
  (define vars (remove #f (sli-vars sli)))
  (define simple-system
    (for/fold ([system sli]) ([x vars])
      (sli-elim-var system x)))
  (andmap leq-trivially-valid? simple-system))


(module+ test
  ; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
  (check-true (sli-satisfiable? (sli (leq (lexp (3 'x) (2 'y))
                                          (lexp (7 #f)))
                                     (leq (lexp (6 'x) (4 'y))
                                          (lexp (15 #f)))
                                     (leq (lexp (-1 'x))
                                          (lexp (1 #f)))
                                     (leq (lexp (0 #f))
                                          (lexp (2 'y))))))


  ; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
  (check-false (sli-satisfiable? (sli (leq (lexp (3 'x) (2 'y))
                                           (lexp (4 #f)))
                                      (leq (lexp (1 #f))
                                           (lexp (1 'x)))
                                      (leq (lexp (1 #f))
                                           (lexp (1 'y)))))))

;**********************************************************************
; Logical Implication for Integer Linear Inequalities
;**********************************************************************

; sli-implies-leq
(define (sli-proves-leq? system ineq)
  (not (sli-satisfiable? (cons (leq-negate ineq)
                               system))))

(module+ test
  ; transitivity! x <= y /\ y <= z --> x <= z
  (check-true (sli-proves-leq? (sli (leq (lexp (1 'x))
                                         (lexp (1 'y)))
                                    (leq (lexp (1 'y))
                                         (lexp (1 'z))))
                               (leq (lexp (1 'x))
                                    (lexp (1 'z)))))


  ; x  <= x;
  (check-true (sli-proves-leq? empty-sli
                               (leq (lexp (1 'x))
                                    (lexp (1 'x)))))

  ; x  - 1 <= x + 1;
  (check-true (sli-proves-leq? empty-sli
                               (leq (lexp (1 'x) (-1 #f))
                                    (lexp (1 'x) (1 #f)))))


  ; x + y <= z; 1 <= y; 0 <= x --> x + 1 <= z
  (check-true (sli-proves-leq? (sli (leq (lexp (1 'x) (1 'y))
                                         (lexp (1 'z)))
                                    (leq (lexp (1 #f))
                                         (lexp (1 'y)))
                                    (leq (lexp)
                                         (lexp (1 'x))))
                               (leq (lexp (1 'x) (1 #f))
                                    (lexp (1 'z))))))

;**********************************************************************
; Logical Implication for Systems of Integer Linear Inequalities
;**********************************************************************

; sli-implies-integer-sli
(define (sli-proves-sli? assumptions goals)
  (andmap (λ (ineq) (sli-proves-leq? assumptions ineq))
          goals))


(module+ test
  ;; 4 <= 3 is false
  (check-false (sli-proves-sli? empty-sli
                                (sli (leq (lexp (4 #f))
                                          (lexp (3 #f))))))
  ;; P and ~P --> false
  (check-true (sli-proves-sli? (sli (leq (lexp) (lexp (1 'y)))
                                    (leq-negate (leq (lexp) (lexp (1 'y)))))
                               (sli (leq (lexp (4 #f))
                                         (lexp (3 #f))))))


  ;; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
  (check-true (sli-proves-sli? (sli (leq (lexp (1 'x) (1 'y))
                                         (lexp (1 'z)))
                                    (leq (lexp)
                                         (lexp (1 'y)))
                                    (leq (lexp)
                                         (lexp (1 'x))))
                               (sli (leq (lexp (1 'x))
                                         (lexp (1 'z)))
                                    (leq (lexp (1 'y))
                                         (lexp (1 'z))))))

  ;; x + y <= z; 0 <= y; 0 <= x -/-> x <= z /\ y <= q
  (check-false (sli-proves-sli? (sli (leq (lexp (1 'x) (1 'y))
                                          (lexp (1 'z)))
                                     (leq (lexp)
                                          (lexp (1 'y)))
                                     (leq (lexp)
                                          (lexp (1 'x))))
                                (sli (leq (lexp (1 'x))
                                          (lexp (1 'z)))
                                     (leq (lexp (1 'y))
                                          (lexp (1 'q))))))

  ;; 7x <= 29 --> x <= 4
  (check-true (sli-proves-sli? (sli (leq (lexp (7 'x))
                                         (lexp (29 #f))))
                               (sli (leq (lexp (1 'x))
                                         (lexp (4 #f))))))
  ;; 7x <= 28 --> x <= 4
  (check-true (sli-proves-sli? (sli (leq (lexp (7 'x))
                                         (lexp (28 #f))))
                               (sli (leq (lexp (1 'x))
                                         (lexp (4 #f))))))
  ;; 7x <= 28 does not --> x <= 3
  (check-false (sli-proves-sli? (sli (leq (lexp (7 'x))
                                          (lexp (28 #f))))
                                (sli (leq (lexp (1 'x))
                                          (lexp (3 #f))))))


  ;; 7x <= 27 --> x <= 3
  (check-true (sli-proves-sli? (sli (leq (lexp (7 'x))
                                         (lexp (27 #f))))
                               (sli (leq (lexp (1 'x))
                                         (lexp (3 #f))))))

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
  (check-true (sli-proves-sli? (sli (leq (lexp (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
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
                               (sli (leq (lexp (0 #f))
                                         (lexp (1 't))))))

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
  (check-false (sli-proves-sli? (sli (leq (lexp (4 'x) (3 'y) (9 'z) (20 'q) (-100 'r) (42 #f))
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
                                (sli (leq (lexp (1 't))
                                          (lexp (0 #f)))))))
