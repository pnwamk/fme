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

(require racket/list racket/bool 
         racket/contract racket/match
         racket/format)
(module+ test
    (require rackunit))

(provide (all-defined-out))

;**********************************************************************
; Linear Expression  (lexp)
; ax + by + cz + ...
;   (and related operations)
;**********************************************************************

(struct constant () #:transparent)
(define CONST (constant))

(define lexp? 
  (λ (a) (and (hash? a)
              (andmap exact-integer? (hash-values a)))))

(define-syntax-rule (lexp t ...)
  (list->lexp (list t ...)))

(define/contract (list->lexp terms)
  (-> (listof (or/c exact-integer? (list/c exact-integer? any/c))) lexp?)
  (define coef first) 
  (define var second)
  (let loop ([h (hash)]
             [zxs terms])
    (match zxs
      ['() h]
      [(cons (? exact-integer? z) zxs-rest)
       (if (zero? z)
           (loop h zxs-rest)
           (loop (hash-update h CONST (λ (c) (+ c z)) 0) zxs-rest))]
      [(cons (list z x) zxs-rest)
       (if (zero? z)
           (loop h zxs-rest)
           (loop (hash-update h x (λ (c) (+ c z)) 0) zxs-rest))])))

; lexp-coefficient
(define/contract (lexp-coefficient exp var)
  (-> lexp? any/c exact-integer?)
  (hash-ref exp var 0))

; lexp-constant
(define/contract (lexp-constant exp)
  (-> lexp? exact-integer?)
  (hash-ref exp CONST 0))

;; lexp-equal?
(define/contract (lexp-equal? l1 l2)
  (-> lexp? lexp? boolean?)
  (for/and ([key (union (hash-keys l1) (hash-keys l2))])
    (= (lexp-coefficient l1 key)
       (lexp-coefficient l2 key))))

(module+ test
  (check-equal? (lexp 0) (lexp 0 '(0 x) '(0 y) '(0 z)))
  
  (check-equal? (lexp-coefficient (lexp 1 '(1 x) '(42 y)) 'y) 42)
  (check-equal? (lexp-constant (lexp 1 '(1 x) '(42 y))) 1)
  (check-equal? (lexp-coefficient (lexp 0 '(1 x) '(42 y)) 'q) 0))


(define/contract (lexp-vars exp)
  (-> lexp? list?)
  (remove CONST (hash-keys exp)))

(module+ test
  (check-not-false (let ([vars (lexp-vars (lexp 17 '(42 x) '(2 z)))])
                     (and (= (length vars) 2)
                          (member 'x vars)
                          (member 'z vars)))))

; lexp-scale
(define/contract (lexp-scale exp a)
  (-> lexp? exact-integer? lexp?)
  (for/hash ([x (cons CONST (lexp-vars exp))])
    (values x (* a (lexp-coefficient exp x)))))

(module+ test
  (check-equal? (lexp-set (lexp 17 '(42 x)) 'x 0)
                (lexp 17)))

; lexp-set
; excludes items set to 0
(define/contract (lexp-set exp var scalar)
  (-> lexp? any/c exact-integer? lexp?)
  (if (zero? scalar)
      (hash-remove exp var)
      (hash-set exp var scalar)))

; lexp-set-constant
; will not insert 0
(define/contract (lexp-set-constant exp scalar)
  (-> lexp? exact-integer? lexp?)
  (if (zero? scalar)
      (hash-remove exp CONST)
      (hash-set exp CONST scalar)))

(module+ test 
  (check-true (lexp-equal? (lexp-set (lexp 17) 'x 42)
                           (lexp 17 '(42 x))))
  (check-true (lexp-equal? (lexp-set (lexp 17 '(2 x)) 'x 42)
                           (lexp 17 '(42 x))))
  (check-true (lexp-equal? (lexp-set-constant (lexp 17 '(2 x)) 42)
                           (lexp 42 '(2 x)))))

; lexp-zero?
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
    (for/fold ([exp (lexp-set-constant exp1 (- (lexp-constant exp1)
                                               (lexp-constant exp2)))]) 
              ([x vars])
    (let* ([s1 (lexp-coefficient exp1 x)]
           [s2 (lexp-coefficient exp2 x)]
           [snew (- s1 s2)])
      (lexp-set exp x snew))))

;; lexp-add
(define/contract (lexp-add exp1 exp2)
  (-> lexp? lexp? lexp?)
  (lexp-subtract exp1 (lexp-scale exp2 -1)))

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
  (not (zero? (lexp-coefficient exp x))))

(module+ test
  (check-false (lexp-has-var? (lexp 17 '(42 x)) 'y))
  (check-not-false (lexp-has-var? (lexp 17 '(42 x)) 'x)))

; lexp-add1
(define/contract (lexp-add1 exp)
  (-> lexp? lexp?)
  (lexp-set exp CONST (add1 (lexp-constant exp))))

(module+ test 
  (check-equal? (lexp-add1 (lexp 0)) (lexp 1))
  (check-true (lexp-equal? (lexp-add1 (lexp 1 '(5 x))) 
                           (lexp 2 '(5 x)))))

; lexp-subst
(define/contract (lexp-subst exp new old)
  (-> lexp? any/c any/c lexp?)
  (if (lexp-has-var? exp old)
      (lexp-set (lexp-set exp old 0) new (lexp-coefficient exp old))
      exp))

(module+ test
  (check-true (lexp-equal? (lexp-subst (lexp 1 '(5 x) '(42 z)) 'y 'x) 
                             (lexp 1 '(5 y) '(42 z)))))

; lexp-subst-lexp
(define/contract (lexp-subst-lexp host-exp exp old-var)
  (-> lexp? lexp? any/c lexp?)
  (if (lexp-has-var? host-exp old-var)
      (lexp-add (lexp-set host-exp old-var 0)
                (lexp-scale exp (lexp-coefficient host-exp old-var)))
      host-exp))

;; lexp->string
(define/contract (lexp->string e [pp #f])
  (-> lexp? (-> any/c any/c) string?)
  (define vars (lexp-vars e))
  (define const (lexp-constant e))
  (define term->string 
    (λ (x) (string-append (if (= 1 (lexp-coefficient e x))
                              ""
                              (number->string (lexp-coefficient e x)))
                           "(" (if pp
                                   (pp x)
                                   (~a x)) ")")))
  (cond
    [(empty? vars) (number->string const)]
    [(zero? const)
     (for/fold ([str (term->string (first vars))])
               ([var (rest vars)])
       (string-append str " + " (term->string var)))]
    [else
     (for/fold ([str (number->string const)])
               ([var vars])
       (string-append str " + " (term->string var)))]))

;**********************************************************************
; Linear Inequalities  (leq)
; a1x1 + a1x2 + ... <= b1y1 + b2y2 + ...
;   (and related operations)
;**********************************************************************

; leq def
(struct Leq (lhs rhs) #:transparent
  #:guard (λ (l r name)
            (unless (and (lexp? l)
                         (lexp? r))
              (error "invalid linear inequality"))
            (values l r)))

; leq-exps
(define/contract (leq-exps ineq)
  (-> Leq? (values lexp? lexp?))
  (values (Leq-lhs ineq) (Leq-rhs ineq)))

;; leq-equal?
(define/contract (leq-equal? l1 l2)
  (-> Leq? Leq? boolean?)
  (define-values (l1lhs l1rhs) (leq-exps l1))
  (define-values (l2lhs l2rhs) (leq-exps l2))
  (and (lexp-equal? l1lhs l2lhs)
       (lexp-equal? l1rhs l2rhs)))


; leq-contains-var
(define/contract (leq-contains-var? ineq var)
  (-> Leq? any/c boolean?)
  (or (lexp-has-var? (Leq-lhs ineq) var)
      (lexp-has-var? (Leq-rhs ineq) var)))

(define (union l1 l2)
  (cond
    [(empty? l1) l2]
    [(member (first l1) l2)
     (union (rest l1) l2)]
    [else
     (union (rest l1) (cons (first l1) l2))]))

; leq-vars
(define/contract (leq-vars ineq)
  (-> Leq? list?)
  (union (lexp-vars (Leq-lhs ineq))
         (lexp-vars (Leq-rhs ineq))))

; leq-negate
; ~ (l1 <= l2) ->
; l2 <= 1 + l1 
; (obviously this is valid for integers only)
(define (leq-negate ineq)
  (-> Leq? Leq?)
  (Leq (lexp-add1 (Leq-rhs ineq))
       (Leq-lhs ineq)))

(module+ test
  (check-true (leq-equal? (leq-negate (Leq (lexp 0 '(1 x))
                                            (lexp 0 '(1 y))))
                           (Leq (lexp 1 '(1 y))
                                (lexp 0 '(1 x))))))
; leq-isolate-var
; converts leq with x into either:
;  1) ax <= by + cz + ...
;  or
;  2) by + cz + ... <= ax
;  where a is a positive integer and x is on at most 
;  one side of the inequality
(define (leq-isolate-var ineq x)
  (-> Leq? any/c)
  (define-values (lhs rhs) (leq-exps ineq))
  ; ... + ax + .... <= ... + bx + ...
  (define a (lexp-coefficient lhs x))
  (define b (lexp-coefficient rhs x))
  (cond
    [(and a b (= a b))
     (Leq (lexp-set lhs x 0)
          (lexp-set rhs x 0))]
    [(and a b (< a b))
     (Leq (lexp-set (lexp-subtract lhs rhs) x 0)
          (lexp `(,(- b a) ,x)))]
    [(and a b (> a b))
     (Leq (lexp `(,(- a b) ,x))
          (lexp-subtract (lexp-set rhs x 0)
                         (lexp-set lhs x 0)))]
    [else
     ineq]))

; x lhs
(module+ test
  (check-equal? (leq-isolate-var (Leq (lexp '(3 x) '(2 z) '(5 y))
                                      (lexp '(1 x) '(1 z)))
                                 'x)
                (Leq (lexp '(2 x)) (lexp '(-5 y) '(-1 z))))
  
  ;; x rhs
  (check-equal? (leq-isolate-var (Leq (lexp '(3 x) '(2 z) '(5 y))
                                      (lexp '(1 z) '(33 x)))
                                 'x)
                (Leq (lexp '(1 z) '(5 y)) (lexp '(30 x))))
  ;; x eq
  (check-equal? (leq-isolate-var (Leq (lexp '(42 x) '(2 z) '(5 y))
                                      (lexp '(42 x) '(1 z)))
                                 'x)
                (Leq (lexp '(2 z) '(5 y))
                     (lexp '(1 z))))
  ;; no x
  (check-equal? (leq-isolate-var (Leq (lexp '(2 z) '(5 y))
                                      (lexp '(1 z)))
                                 'x)
                (Leq (lexp '(2 z) '(5 y))
                     (lexp '(1 z))))

                                        ; x mix
  (check-equal? (leq-isolate-var (Leq (lexp '(2 x) '(4 y) 1)
                                      (lexp '(2 y))) 'x)
                (Leq (lexp '(2 x))
                     (lexp -1 '(-2 y)))))


; leq-join
; takes a pair a1x <= l1 and l2 <= a2x
; and returns a2l1 <= a1l2
(define/contract (leq-join leq1 leq2 x)
  (-> Leq? Leq? any/c Leq?)
  (define-values (lhs1 rhs1) (leq-exps leq1))
  (define-values (lhs2 rhs2) (leq-exps leq2))
  (cond
    ; leq1: a1x <= l1
    ; leq2: l2 <= a2x
    [(and (lexp-coefficient lhs1 x) (zero? (lexp-coefficient rhs1 x))
          (lexp-coefficient rhs2 x) (zero? (lexp-coefficient lhs2 x)))
     (let ([a1 (lexp-coefficient lhs1 x)]
           [a2 (lexp-coefficient rhs2 x)])
       (Leq (lexp-scale lhs2 a1)
            (lexp-scale rhs1 a2)))]
    ; leq1: l1 <= a1x
    ; leq2: a2x <= l2
    [(and (lexp-coefficient rhs1 x) (zero? (lexp-coefficient lhs1 x))
          (lexp-coefficient lhs2 x) (zero? (lexp-coefficient rhs2 x)))
     (let ([a1 (lexp-coefficient rhs1 x)]
           [a2 (lexp-coefficient lhs2 x)])
       (Leq (lexp-scale lhs1 a2)
            (lexp-scale rhs2 a1)))]
    [else
     (error 'leq-join "bad pair for joining by ~a: ~a, ~a" x leq1 leq2)]))

(module+ test 
  (check-equal? (leq-join (Leq (lexp '(2 x))
                               (lexp '(4 y) 10))
                          (Leq (lexp '(4 z) 2)
                               (lexp '(4 x)))
                          'x)
                (Leq (lexp '(8 z) 4)
                     (lexp '(16 y) 40))))


; trivially-valid?
; requires an inequality over constants only
(define/contract (leq-trivially-valid? ineq)
  (-> (and/c Leq? (λ (ineq) (empty? (leq-vars ineq))))
      boolean?)
  (define lhs-val (lexp-coefficient (Leq-lhs ineq) CONST))
  (define rhs-val (lexp-coefficient (Leq-rhs ineq) CONST))
  (<= lhs-val rhs-val))


; leq-subst
(define/contract (leq-subst ineq new old)
  (-> Leq? any/c any/c Leq?)
  (Leq (lexp-subst (Leq-lhs ineq) new old)
       (lexp-subst (Leq-rhs ineq) new old)))

(module+ test
  (check-equal? (leq-subst (leq-subst (Leq (lexp '(1 x))
                                           (lexp '(1 y)))
                                      'y2 
                                      'y)
                           'x2
                           'x)
                (Leq (lexp '(1 x2))
                     (lexp '(1 y2)))))

; leq-subst
(define/contract (leq-subst-lexp ineq new-lexp old-var)
  (-> Leq? lexp? any/c Leq?)
  (Leq (lexp-subst-lexp (Leq-lhs ineq) new-lexp old-var)
       (lexp-subst-lexp (Leq-rhs ineq) new-lexp old-var)))

(define/contract (leq->string ineq [pp #f])
  (-> Leq? (-> any/c any/c) string?)
  (define-values (lhs rhs) (leq-exps ineq))
  (string-append (lexp->string lhs pp) " ≤ " (lexp->string rhs pp)))

;**********************************************************************
; Systems of Integer Linear Inequalities (sli)
; a1x1 + a2x2 + ... <= b1y1 + b2y2 + ...
; c1z1 + c2z2 + ... <= d1q1 + d2q2 + ...
; ...
;   (and related operations)
;**********************************************************************

(define/contract (sli->string sli)
  (-> (listof Leq?) string?)
  (string-append 
   (cond
     [(empty? sli) "("]
     [else
      (for/fold ([str (leq->string (first sli))])
                ([ineq (rest sli)])
        (string-append str " ∧ "(leq->string (first sli))))])
   ")"))

; sli-vars
(define/contract (sli-vars sli)
  (-> (listof Leq?) list?)
  (foldl union empty (map leq-vars sli)))

(module+ test
  (check-equal? (sli-vars (list (Leq (lexp '(1 x))
                                   (lexp '(1 y)))
                              (Leq (lexp '(1 x) '(1 z))
                                   (lexp '(1 q)))
                              (Leq (lexp '(1 r) '(3 z))
                                   (lexp '(1 x)))))
                '(r q z y x)))

; sli-subst
(define/contract (sli-subst sli new old)
  (-> (listof Leq?) any/c any/c (listof Leq?))
  (map (λ (x) (leq-subst x new old)) sli))

; sli-subst-lexp
(define/contract (sli-subst-lexp sli new-lexp old-var)
  (-> (listof Leq?) lexp? any/c (listof Leq?))
  (map (λ (x) (leq-subst-lexp x new-lexp old-var)) sli))

; sli-partition
; partitions leq expressions into
; 3 lists of x-normalized inequalities:
;  value 1) list of (ax <= by + cz + ...) leqs
;  value 2) list of form (by + cz + ... <= ax) leqs
;  value 3) leqs w/o x
(define/contract (sli-partition leqs x)
  (-> (listof Leq?) any/c (values (listof Leq?) (listof Leq?) (listof Leq?)))
  (define nleqs (map (λ (ineq) (leq-isolate-var ineq x)) leqs))
  (for/fold ([xslhs empty]
             [xsrhs empty]
             [noxs empty]) ([ineq nleqs])
    (cond
      [(lexp-has-var? (Leq-lhs ineq) x)
       (values (cons ineq xslhs) xsrhs noxs)]
      [(lexp-has-var? (Leq-rhs ineq) x)
       (values xslhs (cons ineq xsrhs) noxs)]
      [else
       (values xslhs xsrhs (cons ineq noxs))])))

(module+ test
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (list (Leq (lexp '(2 x) '(4 y) 1)
                                                        (lexp '(2 y)))) 
                                              'x)])
                  (list lt gt no))
                (list (list (Leq (lexp '(2 x)) 
                                 (lexp '(-2 y) -1)))
                      empty
                      empty))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (list (Leq (lexp '(2 x) '(4 y) 1)
                                                        (lexp '(2 y)))
                                                   (Leq (lexp '(2 x) '(4 y))
                                                        (lexp '(2 y) '(42 x)))) 
                                              'x)])
                  (list lt gt no))
                (list (list (Leq (lexp '(2 x)) 
                                 (lexp '(-2 y) -1)))
                      (list (Leq (lexp '(2 y))
                                 (lexp '(40 x))))
                      empty))
  (check-equal? (let-values ([(lt gt no)
                              (sli-partition  (list (Leq (lexp '(2 x) '(4 y) -1)
                                                        (lexp '(2 y)))
                                                   (Leq (lexp '(2 x) '(4 y))
                                                        (lexp '(2 y) '(42 x)))
                                                   (Leq (lexp '(2 z) '(4 y))
                                                        (lexp '(2 y) '(42 q)))) 
                                              'x)])
                  (list lt gt no))
                (list (list (Leq (lexp '(2 x)) 
                                (lexp '(-2 y) 1)))
                      (list (Leq (lexp '(2 y))
                                (lexp '(40 x))))
                      (list (Leq (lexp '(2 z) '(4 y))
                                (lexp '(2 y) '(42 q)))))))


; cartesian-map
; map of f over each pair of cartesian
; product of input lists
; order not guaranteed
(define/contract (cartesian-map f xs ys)
  (-> procedure? list? list? list?)
  (for*/fold ([result empty]) ([x xs] [y ys])
    (cons (f x y) result)))


; eliminate-var
; reduces the system of linear inequalties,
; removing x
(define/contract (sli-elim-var sli x)
  (-> (listof Leq?) any/c (listof Leq?))
  (define-values (xltleqs xgtleqs noxleqs) (sli-partition sli x))
  (append (cartesian-map (λ (leq1 leq2) (leq-join leq1 leq2 x)) 
                         xltleqs 
                         xgtleqs)
          noxleqs))

; sli-satisfiable?
(define/contract (sli-satisfiable? sli)
  (-> (listof Leq?) boolean?)
  (define vars (sli-vars sli))
  (define simple-system
    (for/fold ([system sli]) ([x vars])
      (sli-elim-var system x)))
  (andmap leq-trivially-valid? simple-system))


(module+ test
  ; 3x + 2y <= 7; 6x + 4y <= 15;  -x <= 1; 0 <= 2y has integer solutions
  (check-true (sli-satisfiable? (list (Leq (lexp '(3 x) '(2 y))
                                           (lexp 7))
                                     (Leq (lexp '(6 x) '(4 y))
                                          (lexp 15))
                                     (Leq (lexp '(-1 x))
                                          (lexp 1))
                                     (Leq (lexp 0)
                                          (lexp '(2 y))))))


  ; 3x + 2y <= 4; 1 <= x; 1 <= y no solutions 
  (check-false (sli-satisfiable? (list (Leq (lexp '(3 x) '(2 y))
                                           (lexp 4))
                                      (Leq (lexp 1)
                                           (lexp '(1 x)))
                                      (Leq (lexp 1)
                                           (lexp '(1 y)))))))

;**********************************************************************
; Logical Implication for Integer Linear Inequalities
;**********************************************************************

; sli-implies-leq
(define/contract (sli-proves-leq? system ineq)
  (-> (listof Leq?) Leq? boolean?)
  (not (sli-satisfiable? (cons (leq-negate ineq)
                               system))))

(module+ test
  ; transitivity! x <= y /\ y <= z --> x <= z
  (check-true (sli-proves-leq? (list (Leq (lexp '(1 x))
                                         (lexp '(1 y)))
                                    (Leq (lexp '(1 y))
                                         (lexp '(1 z))))
                               (Leq (lexp '(1 x))
                                    (lexp '(1 z)))))


  ; x  <= x;
  (check-true (sli-proves-leq? empty
                               (Leq (lexp '(1 x))
                                    (lexp '(1 x)))))

  ; x  - 1 <= x + 1;
  (check-true (sli-proves-leq? empty
                               (Leq (lexp '(1 x) -1)
                                    (lexp '(1 x) 1))))


  ; x + y <= z; 1 <= y; 0 <= x --> x + 1 <= z
  (check-true (sli-proves-leq? (list (Leq (lexp '(1 x) '(1 y))
                                         (lexp '(1 z)))
                                    (Leq (lexp 1)
                                         (lexp '(1 y)))
                                    (Leq (lexp)
                                         (lexp '(1 x))))
                               (Leq (lexp '(1 x) 1)
                                    (lexp '(1 z))))))

;**********************************************************************
; Logical Implication for Systems of Integer Linear Inequalities
;**********************************************************************

; sli-implies-integer-sli
(define/contract (sli-proves-sli? assumptions goals)
  (-> (listof Leq?) (listof Leq?) boolean?)
  (andmap (λ (ineq) (sli-proves-leq? assumptions ineq))
          goals))


(module+ test
  ;; 4 <= 3 is false
  (check-false (sli-proves-sli? empty
                                (list (Leq (lexp 4)
                                          (lexp 3)))))
  ;; P and ~P --> false
  (check-true (sli-proves-sli? (list (Leq (lexp) (lexp '(1 y)))
                                    (leq-negate (Leq (lexp) (lexp '(1 y)))))
                               (list (Leq (lexp 4)
                                         (lexp 3)))))


  ;; x + y <= z; 0 <= y; 0 <= x --> x <= z /\ y <= z
  (check-true (sli-proves-sli? (list (Leq (lexp '(1 x) '(1 y))
                                         (lexp '(1 z)))
                                    (Leq (lexp)
                                         (lexp '(1 y)))
                                    (Leq (lexp)
                                         (lexp '(1 x))))
                               (list (Leq (lexp '(1 x))
                                          (lexp '(1 z)))
                                     (Leq (lexp '(1 y))
                                          (lexp '(1 z))))))

  ;; x + y <= z; 0 <= y; 0 <= x -/-> x <= z /\ y <= q
  (check-false (sli-proves-sli? (list (Leq (lexp '(1 x) '(1 y))
                                          (lexp '(1 z)))
                                     (Leq (lexp)
                                          (lexp '(1 y)))
                                     (Leq (lexp)
                                          (lexp '(1 x))))
                                (list (Leq (lexp '(1 x))
                                          (lexp '(1 z)))
                                     (Leq (lexp '(1 y))
                                          (lexp '(1 q))))))

  ;; 7x <= 29 --> x <= 4
  (check-true (sli-proves-sli? (list (Leq (lexp '(7 x))
                                         (lexp 29)))
                               (list (Leq (lexp '(1 x))
                                         (lexp 4)))))
  ;; 7x <= 28 --> x <= 4
  (check-true (sli-proves-sli? (list (Leq (lexp '(7 x))
                                         (lexp 28)))
                               (list (Leq (lexp '(1 x))
                                         (lexp 4)))))
  ;; 7x <= 28 does not --> x <= 3
  (check-false (sli-proves-sli? (list (Leq (lexp '(7 x))
                                          (lexp 28)))
                                (list (Leq (lexp '(1 x))
                                          (lexp 3)))))


  ;; 7x <= 27 --> x <= 3
  (check-true (sli-proves-sli? (list (Leq (lexp '(7 x))
                                         (lexp 27)))
                               (list (Leq (lexp '(1 x))
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
  (check-true (sli-proves-sli? (list (Leq (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                          (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                                     (Leq (lexp '(1 x))
                                          (lexp '(1 y) '(1 z)))
                                     (Leq (lexp '(29 r))
                                          (lexp '(1 x) '(1 y) '(1 z) '(1 q)))
                                     (Leq (lexp)
                                          (lexp '(1 x)))
                                     (Leq (lexp)
                                          (lexp '(1 x) '(1 y) '(1 z)))
                                     (Leq (lexp)
                                          (lexp '(1 x) '(1 z)))
                                     (Leq (lexp '(1 x))
                                          (lexp '(1 z)))
                                     (Leq (lexp '(1 z) 1)
                                          (lexp '(1 t)))
                                     (Leq (lexp)
                                          (lexp '(1 x) '(1 y)))
                                     (Leq (lexp)
                                          (lexp '(1 x) '(1 r)))
                                     (Leq (lexp)
                                          (lexp '(1 x) '(1 r) '(1 q))))
                               (list (Leq (lexp)
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
  (check-false (sli-proves-sli? (list (Leq (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(-100 r) 42)
                                           (lexp '(4 x) '(3 y) '(9 z) '(20 q) '(100 r)))
                                      (Leq (lexp '(1 x))
                                           (lexp '(1 y) '(1 z)))
                                      (Leq (lexp '(29 r))
                                           (lexp '(1 x) '(1 y) '(1 z) '(1 q)))
                                      (Leq (lexp)
                                           (lexp '(1 x)))
                                      (Leq (lexp)
                                           (lexp '(1 x) '(1 y) '(1 z)))
                                      (Leq (lexp)
                                           (lexp '(1 x) '(1 z)))
                                      (Leq (lexp '(1 x))
                                           (lexp '(1 z)))
                                      (Leq (lexp '(1 z) 1)
                                           (lexp '(1 t)))
                                      (Leq (lexp)
                                           (lexp '(1 x) '(1 y)))
                                      (Leq (lexp)
                                           (lexp '(1 x) '(1 r)))
                                      (Leq (lexp)
                                           (lexp '(1 x) '(1 r) '(1 q))))
                                (list (Leq (lexp '(1 t))
                                           (lexp))))))
