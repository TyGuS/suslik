From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll0 of x == 0 of
    s = nil /\ h = empty
| sll1 of x != 0 of
  exists nxt s1 v,
  exists h',
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h' /\ sll nxt s1 h'
.
Definition sll_singleton_type :=
  forall (x : nat) (p : ptr),
  {(a : nat)},
    STsep (
      fun h =>
          h = p :-> a,
      [vfun (_: unit) h =>
        exists y (elems : seq nat),
        exists h',
          elems = [:: x] /\ h = p :-> y \+ h' /\ sll y elems h'      ]).
Program Definition sll_singleton : sll_singleton_type :=
  fun x p =>
    Do (
  y2 <-- allocb null 2;
  p ::= y2;;
  (y2 .+ 1) ::= null;;
  y2 ::= x;;
  ret tt    ).
Next Obligation.
ssl_ghostelim_pre.
move=>a//=.
move=>[->].
move=>H_valid.
step.
move=>y2//=.


ssl_write.
Fail ssl_write_post p.
(* TODO: further generalize ssl_write_post *)
rewrite ?unitL.
rewrite ?unitR.
put_to_head (p :-> y2).
match goal with
| [ |- verify (p :-> _ \+ _) _ _ ] =>
  rewrite ?(joinC (p :-> _))
| [ |- verify (p :-> _)  _ _ ] =>
  rewrite -(unitL (p :-> _))
end.
rewrite ?joinA;
apply frame.

ssl_write.
Fail ssl_write_post (y2 .+ 1).
(* TODO: further generalize ssl_write_post *)
rewrite ?joinA;
apply frame.

ssl_write.
ssl_write_post y2.

apply: val_ret; rewrite !unitL=>v1 v2 v3 v4/=.
exists y2, [::x], (y2 :-> x \+ y2 .+ 1 :-> null).
split=>//; split=>//.
- by rewrite joinA joinC joinA. 
- constructor 2=>//; first by rewrite defPtUnO in v2; case/andP: v2=>//.
  exists null, [::], x, Unit; split=>//; rewrite unitR. 
  split=>//.  
  constructor 1=>//.
Qed.
