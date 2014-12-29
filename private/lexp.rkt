#lang racket/base

;; *****************************************************************************
;; lexp.rkt
;; linear expressions (e.g. ax_1 + bx_2 ... ) and related ops.
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
         racket/contract
         racket/match
         racket/set
         racket/format)

(provide (except-out (all-defined-out)
                         lexp
                         lexp-c
                         lexp-var-map
                         hash-set-var
                         make-lexp
                         lexp*)
         (rename-out [lexp* lexp]))

(define-struct/cond-contract lexp 
  ([c exact-integer?] 
   [var-map (hash/c any/c exact-integer? #:immutable #t)]) 
  #:transparent)

(define-syntax-rule (lexp* t ...)
  (list->lexp (list t ...)))

(define/contract (list->lexp terms)
  (-> (listof (or/c exact-integer? (list/c exact-integer? any/c))) lexp?)
  (define coef car)
  (define var cadr)
  (let loop ([c 0]
             [h (hash)]
             [zxs terms])
    (match zxs
      [`() (lexp c h)]
      [`((,a ,x) . ,xs) (loop c (hash-set-var h x (+ a (hash-ref h x 0))) xs)]
      [`(,a . ,xs) (loop (+ a c) h xs)])))


(define/cond-contract (hash-set-var h x i)
  (-> (hash/c any/c exact-integer? #:immutable #t) 
      any/c 
      exact-integer?
      (hash/c any/c exact-integer? #:immutable #t))
  (if (= 0 i)
      (hash-remove h x)
      (hash-set h x i)))

; lexp-coeff
(define/cond-contract (lexp-coeff l x)
  (-> lexp? any/c exact-integer?)
  (hash-ref (lexp-var-map l) x 0))

; lexp-const
(define/cond-contract (lexp-const l)
  (-> lexp? exact-integer?)
  (lexp-c l))

(module+ test
  (require rackunit)
  
  (check-equal? (lexp* 1 '(1 x) '(42 y) 1) (lexp* '(42 y) 2 '(1 x)))
  (check-equal? (lexp* 0) (lexp* 0 '(0 x) '(0 y) '(0 z)))
  (check-equal? (lexp-coeff (lexp* 1 '(1 x) '(42 y)) 'y) 42)
  (check-equal? (lexp-const (lexp* 1 '(1 x) '(42 y))) 1)
  (check-equal? (lexp-coeff (lexp* '(1 x) '(42 y)) 'q) 0))

(define/cond-contract (lexp-vars exp)
  (-> lexp? list?)
  (hash-keys (lexp-var-map exp)))

(define/cond-contract (lexp-scalars exp)
  (-> lexp? list?)
  (define c (lexp-const exp))
  (define coeffs (hash-values (lexp-var-map exp)))
  (if (zero? c) coeffs (cons c coeffs)))

(module+ test
  (check-true (and (equal? (list->set (lexp-vars (lexp* 17 '(42 x) '(2 z))))
                           (list->set '(x z)))
                   (= 2 (length (lexp-vars (lexp* 17 '(42 x) '(2 z)))))))
  (check-true (and (equal? (list->set (lexp-scalars (lexp* 17 '(42 x) '(2 z))))
                           (list->set '(17 42 2)))
                   (= 3 (length (lexp-scalars (lexp* 17 '(42 x) '(2 z))))))))

; lexp-scale
;; if multiplying any scalar by a results
;; in a non integer, error is thrown if
;; contracts are active
(define/cond-contract (lexp-scale exp a)
  (-> lexp? rational? lexp?)
  (define c* (* (lexp-const exp) a))
  (define hash* (for/fold ([h (hash)])
                          ([x (in-list (lexp-vars exp))])
                  (hash-set-var h x (* (lexp-coeff exp x) a))))
  (lexp c* hash*))

(module+ test
  (check-equal? (lexp-set (lexp* 17 '(42 x)) 'x 0)
                (lexp* 17)))
; lexp-set
; excludes items set to 0
(define/cond-contract (lexp-set exp x i)
  (-> lexp? any/c exact-integer? lexp?)
  (lexp (lexp-const exp)
        (hash-set-var (lexp-var-map exp) x i)))

; lexp-set-const
(define/cond-contract (lexp-set-const exp i)
  (-> lexp? exact-integer? lexp?)
  (lexp i
        (lexp-var-map exp)))

(module+ test 
  (check-equal? (lexp-set (lexp* 17) 'x 42)
                (lexp* 17 '(42 x)))
  (check-equal? (lexp-set (lexp* 17 '(2 x)) 'x 42)
                (lexp* 17 '(42 x)))
  (check-equal? (lexp-set-const (lexp* 17 '(2 x)) 42)
                (lexp* 42 '(2 x))))

; lexp-zero?
(define/cond-contract (lexp-zero? exp)
  (-> lexp? boolean?)
  (and (= 0 (lexp-const exp))
       (hash-empty? (lexp-var-map exp))))

(module+ test
  (check-false (lexp-zero? (lexp* 17 '(42 x))))
  (check-false (lexp-zero? (lexp* 17)))
  (check-not-false (lexp-zero? (lexp* 0))))

; l1 - l2
(define/cond-contract (lexp-minus l1 l2)
  (-> lexp? lexp? lexp?)
  (lexp (- (lexp-c l1) (lexp-c l2))
        (for/fold ([h (lexp-var-map l1)])
                  ([x (in-list (lexp-vars l2))])
          (hash-set-var h x (- (lexp-coeff l1 x)
                               (lexp-coeff l2 x))))))

;; l1 + l2
(define/cond-contract (lexp-plus l1 l2)
  (-> lexp? lexp? lexp?)
  (lexp (+ (lexp-c l1) (lexp-c l2))
        (for/fold ([h (lexp-var-map l1)])
                  ([x (in-list (lexp-vars l2))])
          (hash-set-var h x (+ (lexp-coeff l1 x)
                               (lexp-coeff l2 x))))))

(module+ test
  (check-equal? (lexp-minus (lexp* -1 '(2 x) '(3 y))
                            (lexp* -1 '(2 x) '(42 z)))
                (lexp* 0 '(3 y) '(-42 z)))
  (check-equal? (lexp-minus (lexp* 0)
                            (lexp* -1 '(2 x) '(42 z)))
                (lexp* 1 '(-2 x) '(-42 z))))

; lexp-has-var?
(define/cond-contract (lexp-has-var? l x)
  (-> lexp? any/c boolean?)
  (not (zero? (lexp-coeff l x))))

(module+ test
  (check-false (lexp-has-var? (lexp* 17 '(42 x)) 'y))
  (check-not-false (lexp-has-var? (lexp* 17 '(42 x)) 'x)))

; lexp-add1
(define/cond-contract (lexp-add1 l)
  (-> lexp? lexp?)
  (lexp-set-const l (add1 (lexp-const l))))

(module+ test 
  (check-equal? (lexp-add1 (lexp* 0)) (lexp* 1))
  (check-equal? (lexp-add1 (lexp* 1 '(5 x))) 
                (lexp* 2 '(5 x))))

(define/cond-contract (constant-lexp? l)
  (-> lexp? boolean?)
  (hash-empty? (lexp-var-map l)))

#|
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
|#

;; lexp->string
(define/cond-contract (lexp->string e [pp #f])
  (-> lexp? (-> any/c any/c) string?)
  (define vars (lexp-vars e))
  (define const (lexp-const e))
  (define term->string 
    (λ (x) (string-append (if (= 1 (lexp-coeff e x))
                              ""
                              (number->string (lexp-coeff e x)))
                           "(" (if pp
                                   (pp x)
                                   (~a x)) ")")))
  (cond
    [(null? vars) (number->string const)]
    [(zero? const)
     (for/fold ([str (term->string (car vars))])
               ([var (in-list (cdr vars))])
       (string-append str " + " (term->string var)))]
    [else
     (for/fold ([str (number->string const)])
               ([var (in-list vars)])
       (string-append str " + " (term->string var)))]))
