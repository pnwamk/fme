#lang scribble/manual

@require[scribble/eval
         (for-label racket)]


@define[fme-eval (make-base-eval)]
@interaction-eval[#:eval fme-eval (require "main.rkt"
                                           racket/set)]

@title{Fourier-Motzkin Elimination for Integer Systems}
@author+email["Andrew Kent" "andmkent@indiana.edu"]

@defmodule[fme]

This package is a simple functional, algebraic implementation of the Fourier-Motzkin elimination 
method (as opposed to the more common matrix-based approach). 
It reasons about systems of linear inequalties (SLIs) over integers
and currently has two primary functions:

@itemlist[#:style 'ordered
                  @item{Decide the satisfiability of a SLI.}
                  @item{Decide if one SLI implies another.}]


The linear inequalities are of the form (L1 ≤ L2), where L1 and L2 are
simple linear combinations of the form ax + by + ... + c.

@table-of-contents[]

@section{Some Quick Examples}

@examples[#:eval fme-eval
                 (let ([assumptions (set (leq (lexp '(7 x))
                                              (lexp 29)))]
                       [goal (leq (lexp '(1 x)) 
                                  (lexp 4))])
                   (begin (printf "Does ~a imply ~a?" 
                                  (sli->string assumptions)
                                  (leq->string goal))
                          (fme-imp-leq? assumptions goal)))
                 
                 (let ([assumptions (set (leq (lexp '(7 x))
                                              (lexp 29)))]
                       [goal (leq (lexp '(1 x)) (lexp 3))])
                   (begin (printf "Does ~a imply ~a?" 
                                  (sli->string assumptions)
                                  (leq->string goal))
                          (fme-imp-leq? assumptions goal)))
                 
                 (let ([assumptions (set (leq (lexp '(1 x) '(1 y))
                                              (lexp '(1 z)))
                                         (leq (lexp)
                                              (lexp '(1 y)))
                                         (leq (lexp)
                                              (lexp '(1 x))))]
                       [goals (set (leq (lexp '(1 x))
                                        (lexp '(1 z)))
                                   (leq (lexp '(1 y))
                                        (lexp '(1 z)))
                                   (leq (lexp)
                                        (lexp '(1 z))))])
                   (begin (printf "Does ~a \n imply \n~a?" 
                                  (sli->string assumptions)
                                  (sli->string goals))
                          (fme-imp? assumptions goals)))]

@section{Linear Expressions}

@defproc[(lexp [term (or/c integer?
                           (list integer? any/c))] ...)
         lexp?]{
Builds a linear expression from the given terms. Each term is either
a constant @racket[exact-integer?] or a @racket[list] of 
length two representing an integer coefficient and 
it's associated variable (which can be anything, comparisons
are done using equal?).}

@defproc[(lexp? [e any/c])
         boolean?]{
  Returns @racket[#t] if @racket[e] is a linear expression.}

@defproc[(lexp-coeff [e lexp?] [x any/c])
         integer?]{
  Returns the scalar coefficient for the variable 
  @racket[x] in @racket[e], 
  returning @racket[0] if @racket[x] is not present.}


@defproc[(lexp-const [e lexp?])
         integer?]{
  Returns the scalar constant for @racket[e].}

@defproc[(lexp-vars [e lexp?])
         (listof any/c)]{
  Returns a list of the variables in this linear expression (in no particular order).}

@defproc[(lexp-has-var? [e lexp?] [x any/c])
         boolean?]{
  Equivalent to @racket[(not (zero? (lexp-coefficient e x)))].
}

@defproc[(lexp-scalars [e lexp?])
         (listof exact-integer?)]{
  Returns the list of coefficients and the
  scalar constant in @racket[e].
}


@defproc[(lexp-scale [e lexp?] [n integer?])
         lexp?]{
  Returns an @racket[lexp?] equivalent to multiplying all 
             scalars (coefficients and constants) in 
  @racket[e] by @racket[n].
}


@defproc[(lexp-set [e lexp?] [x any/c] [n integer?])
         lexp?]{
  Returns a linear expression equal to @racket[e] 
  except the coefficient for 
  @racket[x] is @racket[n].
}

@defproc[(lexp-set-const [e lexp?] [n integer?])
         lexp?]{
Returns a linear expression equal to 
@racket[e] but with the constant set to @racket[n].
}

@defproc[(lexp-zero? [e lexp?])
         boolean?]{
  Returns @racket[#t] if the linear expression 
          is mathematically equivalent to @racket[0].
}

@defproc[(lexp-minus [e1 lexp?] [e2 lexp?])
         lexp?]{
  Returns the result of @racket[e1] - @racket[e1]. 
  For example (shown below), 
  (2x + 3y - 1) - (2x + 42z - 1) = 3y - 42z
  
  @examples[#:eval fme-eval
                   (lexp->string (lexp-minus (lexp '(2 x) '(3 y) -1)
                                             (lexp '(2 x) -1 '(42 z))))]}

@defproc[(lexp-plus [e1 lexp?] [e2 lexp?])
         lexp?]{
  Adds @racket[e1] @racket[e2].
  
  @examples[#:eval fme-eval
                   (lexp->string (lexp-plus (lexp '(2 x) '(3 y) -1)
                                            (lexp '(2 x) -1 '(42 z))))]}


@defproc[(lexp-add1 [e lexp?])
         lexp?]{
Equivalent to @racket[(lexp-set-const e (add1 (lexp-const e)))].
 
 @examples[#:eval fme-eval
                  (lexp->string (lexp-add1 (lexp 1 '(5 x))))]
}

@;{
@defproc[(lexp-subst [e lexp?] [new any/c] [old any/c])
         lexp?]{
Returns a linear expression equal to @racket[e] but with all occurrences of
@racket[old] replaced with @racket[new].
 
 @examples[#:eval fme-eval
                  (lexp->string (lexp-subst (lexp 1 '(5 x)) 'y 'x))]
}
}

@section{Linear Inequalities}

@defstruct[leq ([lhs lexp?] [rhs lexp?])]{
   A structure representing a less-than-or-equal-to inequality
   of the form lhs ≤ rhs. When constructed, the leq is normalized,
   dividing all scalars by the gcd of all scalars in the leq.}

@defproc[(leq-lexps [ineq leq?])
         (values lexp? lexp?)]{
 Returns the lhs and rhs of the inequality.}

@defproc[(lexp-contains-var? [ineq leq?] [x any/c])
         boolean?]{
 Returns @racket[#t] if @racket[x] is in the lhs or rhs of @racket[ineq], else @racket[#f].}
 
@defproc[(leq-negate [ineq leq?])
         leq?]{
 Negates @racket[ineq] based on integer arithmetic (e.g. not (x ≤ y) implies (y+1 ≤ x)).}

@defproc[(leq-isolate-var [ineq leq?] [x any/c])
         leq?]{
 Converts an inequality into either (a@racket[x] ≤ by + cz + ...) or (by + cz + ... ≤ a@racket[x])
 such that a is a positive integer and @racket[x] appears on at most one side of the inequality.
 If @racket[x] is not in ineq, it is a no-op.}

@defproc[(leq-join [ineq1 leq?] [ineq2 leq?] [x any/c])
         leq?]{
 Takes a pair of inequalities of the forms (a1@racket[x] ≤ l1) and (l2 ≤ a2@racket[x])
 and returns a2l1 ≤ a1l2.}

@defproc[(leq-trivially-valid? [ineq1 leq?] [ineq2 leq?])
         boolean]{
 Checks if (@racket[ineq1] ≤ @racket[ineq2]) is trivially true 
            (i.e. they must both be constants or equal).}

@section{Systems of Linear Inequalities}

@defproc[(sli? [a any/c])
         boolean?]{
  Equivalent to @racket[(setof leq?)].
}


@defproc[(sli-vars [sys sli?])
         (listof any/c)]{
  Returns a list of all of the variables in the inequalities of this system,
  with duplicates removed.
}

@defproc[(sli-partition [sys sli?] [x any/c])
         (values sli? sli? sli?)]{
  3-way partitions @racket[sys] based on how leq-isolate-var would 
  re-order the inequality in terms of @racket[x]:
  @itemlist[@item{Inequalities of the form (a@racket[x] ≤ by + cz + ...)}
             @item{Inequalities of the form (by + cz + ... ≤ a@racket[x])}
             @item{Inequalities which do not contain @racket[x]}
             #:style 'ordered]
}

@section{Fourier-Motzkin Operations}

@defproc[(fme-elim-var [sys sli?] [x any/c])
         sli?]{
  Returns an SLI without @racket[x] such that it possesses the same set 
  of satisfying solutions with respect to the remaining variables.
                        
  It relies on @racket[sli-partition] and @racket[leq-join].
}

@defproc[(fme-sat? [sys sli?])
         boolean?]{
  Reports if a given system of linear inequalities is satisfiable 
  (i.e. does a real number solution exist) using Fourier-Motzkin
  elimination.
}

@defproc[(fme-imp-leq? [sys sli?] [ineq leq?])
         boolean?]{
  Reports if a given system of linear inequalities, @racket[sys], implies
  the constraint @racket[ineq] (this is valid for the integer domain of
  inequalities only, since we utilize integer inequality negation
  and then test for satisfiability).
}

@defproc[(fme-imp? [sys1 sli?] [sys2 sli?])
         boolean?]{
  Reports if @racket[sys1] implies all of the constraints contained in @racket[sys2]
  (again, this is valid for the integer domain of
  inequalities only, since we utilize integer inequality negation).
}
           