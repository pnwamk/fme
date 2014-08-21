#lang scribble/manual

@require[scribble/eval
         (for-label racket)]


@define[fme-eval (make-base-eval)]
@interaction-eval[#:eval fme-eval (require "main.rkt")]

@title{Fourier-Motzkin Elimination for Integer Systems}
@author+email["Andrew Kent" "andmkent@indiana.edu"]}

@defmodule[fme]

This package is a simple implementation of the Fourier-Motzkin elimination 
method. It reasons about systems of linear inequalties (SLIs) and currently
has two primary functions:

@itemlist[#:style 'ordered
                  @item{Decide the satisfiability of a SLI (over reals).}
                  @item{Decide if one SLI implies another (over integers).}]


The linear inequalities are of the form (L1 ≤ L2), where L1 and L2 are
simple linear combinations of the form ax + by + ... + c.


 @table-of-contents[]

@section{Some Quick Examples}

@examples[#:eval fme-eval
                 (let ([assumptions (sli (leq (lexp (7 'x))
                                              (lexp (29 #f))))]
                       [goal (leq (lexp (1 'x)) (lexp (4 #f)))])
                   (if (sli-proves-leq? assumptions goal)
                       (printf "7x ≤ 29\nimplies\nx ≤ 4\n")
                       (printf "7x ≤ 29 \ndoesn't imply\n x ≤ 4")))
                 
                 (let ([assumptions (sli (leq (lexp (7 'x))
                                              (lexp (29 #f))))]
                       [goal (leq (lexp (1 'x)) (lexp (3 #f)))])
                   (if (sli-proves-leq? assumptions goal)
                       (printf "7x ≤ 29 \nimplies\nx ≤ 3")
                       (printf "7x ≤ 29 \ndoesn't imply\nx ≤ 3")))
                 
                 (let ([assumptions (sli (leq (lexp (1 'x) (1 'y))
                                              (lexp (1 'z)))
                                         (leq (lexp)
                                              (lexp (1 'y)))
                                         (leq (lexp)
                                              (lexp (1 'x))))]
                       [goals (sli (leq (lexp (1 'x))
                                        (lexp (1 'z)))
                                   (leq (lexp (1 'y))
                                        (lexp (1 'z)))
                                   (leq (lexp (0 #f))
                                        (lexp (1 'z))))])
                   (if (sli-proves-sli? assumptions goals)
                       (printf "x + y ≤ z ∧ 0 ≤ y ∧ 0 ≤ x \nimplies\nx ≤ z ∧ y ≤ z")
                       (printf "x + y ≤ z ∧ 0 ≤ y ∧ 0 ≤ x \ndoesn't imply\nx ≤ z ∧ y ≤ z ∧ 0 ≤ z")))]



@section{Linear Expressions}

 @defform[(lexp (a x) ...)
          #:contracts ([a exact-integer?]
                       [x any/c])]{
   Returns a linear expression of the form ax+ ... where a is the scalar 
   coefficient and x is the variable. For constants, use #f as the variable.
   (Currently we merely represent these with a hash mapping variables to coefficients)}

@defproc[(lexp? [e any/c])
         boolean?]{
  Tests if argument is a linear expression.
}

@defproc[(lexp-scalar [e lexp?] [x any/c] [default any/c])
         any/c]{
  Returns the scalar coefficient for the variable x in e, 
  or default if x is not present.
  @racket[#f] is used as the variable for constants.
}

@defproc[(lexp-vars [e lexp?])
         (listof any/c)]{
  Returns a list of the variables in this linear expression (in no particular order).
  @racket[#f] is included if the expression has a constant.
}

@defproc[(lexp-has-var? [e lexp?] [x any/c])
         boolean?]{
  Returns @racket[#t] if x is in e, else @racket[#f].
}

@defproc[(lexp-scale [e lexp?] [a exact-integer])
         lexp?]{
  Multiplies all scalar coefficients in e by a.
}

@defproc[(lexp-remove [e lexp?] [x any/c])
         lexp?]{
  Removes the term with the variable x from the linear expression e (no-op if x not present).
}

@defproc[(lexp-set [e lexp?] [x any/c] [a exact-integer?])
         lexp?]{
  Changes the coefficient for x to a (adding x if it is not in the linear equation).
}

@defproc[(lexp-size [e lexp?])
         exact-nonnegative-integer?]{
  Returns the number of terms in the linear expression 
  (i.e. number of unique variables +1 if a constant is present).
}

@defproc[(lexp-empty? [e lexp?])
         boolean?]{
  Reports if the linear expression is entirely empty (i.e. equal to 0).
}


@defproc[(lexp-subtract [e1 lexp?] [e2 lexp?])
         lexp?]{
  Returns the result of e1 - e2. For example (shown below), 
  (2x + 3y - 1) - (2x + 42z - 1) = 3y - 42z
  
  @examples[#:eval fme-eval
                   (lexp-subtract (lexp (2 'x) (3 'y) (-1 #f))
                             (lexp (2 'x) (-1 #f) (42 'z)))]
Note that lexp's use hash tables for their representation, so their values are
printed in the regular hash form.}

@defproc[(lexp-add1 [e lexp?])
         lexp?]{
 Adds 1 to the constant in e.
 
 @examples[#:eval fme-eval
                  (equal? (lexp-add1 (lexp (1 #f) (5 'x))) 
                          (lexp (2 #f) (5 'x)))]
}

@defproc[(lexp-subst [e lexp?] [new any/c] [old any/c])
         lexp?]{
 Substitutes the new variable in for the old.
 
 @examples[#:eval fme-eval
                  (equal? (lexp-subst (lexp (1 #f) (5 'x)) 'y 'x) 
                          (lexp (1 #f) (5 'y)))]
}


@section{Linear Inequalities}

@defstruct[leq ([lhs lexp?] [rhs lexp?])]{
   A structure representing a less-than-or-equal-to inequality
   of the form lhs ≤ rhs.}

@defproc[(leq-exps [ineq leq?])
         (values lexp? lexp?)]{
 Returns the lhs and rhs of the inequality.}

@defproc[(lexp-contains-var? [ineq leq?] [x any/c])
         boolean?]{
 Returns @racket[#t] if x is in the lhs or rhs of ineq, else @racket[#f].}
 
@defproc[(leq-negate [ineq leq?])
         leq?]{
 Negates ineq based on *integer math*, e.g. not (x <= y) implies (y+1 <= x).}

@defproc[(leq-isolate-var [ineq leq?] [x any/c])
         leq?]{
 Converts an inequality into either (ax <= by + cz + ...) or (by + cz + ... <= ax)
 such that a is a positive integer and x appears on at most one side of the inequality.
 If x is not in ineq, it is a no-op.}

@defproc[(leq-join [ineq1 leq?] [ineq2 leq?] [x any/c])
         leq?]{
 Takes a pair of inequalities of the forms (a1x <= l1) and (l2 <= a2x)
 and returns a2l1 <= a1l2.}

@defproc[(leq-trivially-valid? [ineq1 leq?] [ineq2 leq?])
         boolean]{
 Checks if ineq1 <= ineq2 is trivially true (i.e. they must both be constants).}

@section{Systems of Linear Inequalities}

@defproc[(sli [ineq leq?] ...)
         (listof leq?)]{
  Constructor for a system of linear inequalities. Currently just wraps @racket[list].
}

@defproc[(sli-vars [sys (listof leq?)])
         (listof any/c)]{
  Returns a list of all of the variables in the inequalities of this system,
  with duplicates removed.
}

@defproc[(sli-partition [sys (listof leq?)] [x any/c])
         (values (listof leq?) (listof leq?) (listof leq?))]{
  3-way partitions the system of inequalities based on how leq-isolate-var would 
  re-order the inequality in terms of x:
  @itemlist[@item{Inequalities of the form (ax <= by + cz + ...)}
             @item{Inequalities of the form (by + cz + ... <= ax)}
             @item{Inequalities which do not contain x}
             #:style 'ordered]
}

@defproc[(sli-elim-var [sys (listof leq?)] [x any/c])
         (listof leq?)]{
  Reduces the system of linear inequalities, performing the proper algebraic
  eliminations (see sli-partition and leq-join) such that the system no longer
  contains x but maintains the same set of satisfying solutions with respect to
  the remaining variables.
  
  This elimination is sound for *real number* solutions. (Since we are mainly
  concerned with unsatisfiability, however, this is not a huge issue, since if
  a system is unsatisfiable for reals it is also unsatisfiable for integers, thus
  this is also a sound method for checking unsatisfiability of integer problems
  as well).
}

@defproc[(sli-satisfiable? [sys (listof leq?)])
         boolean?]{
  Reports if a given system of linear inequalities is satisfiable 
  (i.e. does a real number solution) exist.
}

@defproc[(sli-proves-leq? [sys (listof leq?)] [ineq leq?])
         boolean?]{
  Reports if a given system of linear inequalities, sys, implies
  the constraint ineq (this is valid for the integer domain of
  inequalities only, since we utilize integer inequality negation).
}

@defproc[(sli-proves-sli? [sys1 (listof leq?)] [sys2 (listof leq?)])
         boolean?]{
  Reports if sys1 implies all of the constraints contained in sys2
  (again, this is valid for the integer domain of
  inequalities only, since we utilize integer inequality negation).
}
           