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

(* TODO translation error: how to translate Suslik subsets into Coq list types? *)
Definition sll_init_type :=
  forall (x : ptr) (v : nat),
  {(s : seq nat)},
    STsep (
      fun h =>
          sll x s h,
      [vfun (_: unit) h =>
        exists s1,
          s1 org.tygus.suslik.certification.targets.coq.language.Expressions$COpSubset$@f88bfbe [:: v] /\ sll x s1 h      ]).

Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) x v =>
    Do (
  ret tt    )).
Next Obligation.
ssl_ghostelim_pre.
move=>s//=.
move=>H_sll.
move=>H_valid.
case: ifP=>H_cond.
case H_sll; rewrite H_cond=>//= _.
move=>[sll_phi].
move=>[->].
ssl_emp.
case H_sll; rewrite H_cond=>//= _.
move=>[nxt] [s1] [v].
move=>[h'].
move=>[sll_phi].
move=>[->].
move=>H_sll0.
case: ifP=>H_cond.
case H_sll; rewrite H_cond=>//= _.
move=>[sll_phi].
move=>[->].
ssl_emp.


Qed.

