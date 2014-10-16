1656
((3) 0 () 2 ((q lib "fme/main.rkt") (q 1057 . 5)) () (h ! (equal) ((c def c (c (? . 0) q struct:leq)) c (? . 1)) ((c def c (c (? . 0) q lexp?)) q (117 . 3)) ((c def c (c (? . 0) q sli-partition)) q (1731 . 5)) ((c def c (c (? . 0) q leq-exps)) q (1168 . 3)) ((c def c (c (? . 0) q lexp-add)) q (832 . 4)) ((c def c (c (? . 0) q lexp-subst)) q (958 . 5)) ((c def c (c (? . 0) q leq-lhs)) c (? . 1)) ((c def c (c (? . 0) q leq-isolate-var)) q (1376 . 4)) ((c def c (c (? . 0) q sli-proves-sli?)) q (2130 . 4)) ((c def c (c (? . 0) q lexp)) q (0 . 4)) ((c def c (c (? . 0) q sli-proves-leq?)) q (2032 . 4)) ((c def c (c (? . 0) q leq-rhs)) c (? . 1)) ((c def c (c (? . 0) q leq)) c (? . 1)) ((c def c (c (? . 0) q lexp-has-var?)) q (370 . 4)) ((c def c (c (? . 0) q sli-vars)) q (1657 . 3)) ((c def c (c (? . 0) q sli-elim-var)) q (1861 . 4)) ((c def c (c (? . 0) q lexp-set-constant)) q (615 . 4)) ((c def c (c (? . 0) q leq-negate)) q (1319 . 3)) ((c def c (c (? . 0) q leq-trivially-valid?)) q (1559 . 4)) ((c def c (c (? . 0) q lexp-vars)) q (308 . 3)) ((c def c (c (? . 0) q leq?)) c (? . 1)) ((c def c (c (? . 0) q lexp-coefficient)) q (168 . 4)) ((c def c (c (? . 0) q lexp-constant)) q (249 . 3)) ((c def c (c (? . 0) q leq-join)) q (1457 . 5)) ((c def c (c (? . 0) q lexp-zero?)) q (697 . 3)) ((c def c (c (? . 0) q lexp-subtract)) q (753 . 4)) ((c def c (c (? . 0) q sli-satisfiable?)) q (1957 . 3)) ((c def c (c (? . 0) q lexp-contains-var?)) q (1231 . 4)) ((c def c (c (? . 0) q lexp-set)) q (523 . 5)) ((c def c (c (? . 0) q make-leq)) c (? . 1)) ((c def c (c (? . 0) q lexp-scale)) q (448 . 4)) ((c def c (c (? . 0) q lexp-add1)) q (906 . 3))))
procedure
(lexp term ...) -> boolean?
  term : (or/c integer?
               (list integer? any/c))
procedure
(lexp? e) -> boolean?
  e : any/c
procedure
(lexp-coefficient e x) -> integer?
  e : lexp?
  x : any/c
procedure
(lexp-constant e) -> integer?
  e : lexp?
procedure
(lexp-vars e) -> (listof any/c)
  e : lexp?
procedure
(lexp-has-var? e x) -> boolean?
  e : lexp?
  x : any/c
procedure
(lexp-scale e n) -> lexp?
  e : lexp?
  n : integer?
procedure
(lexp-set e x n) -> lexp?
  e : lexp?
  x : any/c
  n : integer?
procedure
(lexp-set-constant e n) -> lexp?
  e : lexp?
  n : integer?
procedure
(lexp-zero? e) -> boolean?
  e : lexp?
procedure
(lexp-subtract e1 e2) -> lexp?
  e1 : lexp?
  e2 : lexp?
procedure
(lexp-add e1 e2) -> lexp?
  e1 : lexp?
  e2 : lexp?
procedure
(lexp-add1 e) -> lexp?
  e : lexp?
procedure
(lexp-subst e new old) -> lexp?
  e : lexp?
  new : any/c
  old : any/c
struct
(struct leq (lhs rhs)
    #:extra-constructor-name make-leq)
  lhs : lexp?
  rhs : lexp?
procedure
(leq-exps ineq) -> lexp? lexp?
  ineq : leq?
procedure
(lexp-contains-var? ineq x) -> boolean?
  ineq : leq?
  x : any/c
procedure
(leq-negate ineq) -> leq?
  ineq : leq?
procedure
(leq-isolate-var ineq x) -> leq?
  ineq : leq?
  x : any/c
procedure
(leq-join ineq1 ineq2 x) -> leq?
  ineq1 : leq?
  ineq2 : leq?
  x : any/c
procedure
(leq-trivially-valid? ineq1 ineq2) -> boolean
  ineq1 : leq?
  ineq2 : leq?
procedure
(sli-vars sys) -> (listof any/c)
  sys : (listof leq?)
procedure
(sli-partition sys x)
 -> (listof leq?) (listof leq?) (listof leq?)
  sys : (listof leq?)
  x : any/c
procedure
(sli-elim-var sys x) -> (listof leq?)
  sys : (listof leq?)
  x : any/c
procedure
(sli-satisfiable? sys) -> boolean?
  sys : (listof leq?)
procedure
(sli-proves-leq? sys ineq) -> boolean?
  sys : (listof leq?)
  ineq : leq?
procedure
(sli-proves-sli? sys1 sys2) -> boolean?
  sys1 : (listof leq?)
  sys2 : (listof leq?)
