#lang racket/base

;; *****************************************************************************
;; fme-utils.rkt
;; useful functions for the rest of the fme library
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

(require (for-syntax racket/base syntax/parse)
         racket/contract)

(define-for-syntax enable-contracts? (and (getenv "PLT_FME_CONTRACTS") #t))

(provide (for-syntax enable-contracts?)
         union
         define-struct/cond-contract
         define/cond-contract)

;; list append w/o duplicates
(define (union l1 l2)
  (cond
    [(null? l1) l2]
    [(member (car l1) l2)
     (union (cdr l1) l2)]
    [else
     (union (cdr l1) (cons (car l1) l2))]))

;; a define with contracts if enable-contracts is #t
(define-syntax define/cond-contract
  (if enable-contracts?
      (make-rename-transformer #'define/contract)
      (lambda (stx)
        (syntax-parse stx
          [(_ head cnt . body)
           (syntax/loc stx (define head . body))]))))

;; defines a struct with contracts if enable-contracts is #t
(define-syntax define-struct/cond-contract
  (if enable-contracts?
      (make-rename-transformer #'define-struct/contract)
      (syntax-rules ()
        [(_ hd ([i c] ...) . opts)
         (define-struct hd (i ...) . opts)])))