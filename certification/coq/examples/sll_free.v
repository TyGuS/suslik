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
Definition sll_free_type :=
  forall (x : ptr),
  {(s : seq nat)},
    STsep (
      fun h =>
          sll x s h,
      [vfun (_: unit) h =>
          h = empty      ]).
Program Definition sll_free : sll_free_type :=
  Fix (fun (sll_free : sll_free_type) x =>
    Do (
  if x == 0
  then
    ret tt
  else
    nxtx2 <-- @read ptr (x .+ 1);
    sll_free nxtx2;;
    dealloc (x .+ 1);;
    dealloc x;;
    ret tt
    )).
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
ssl_read.
put_to_head h'.
apply: bnd_seq.
apply: (gh_ex s1).
apply: val_do=>//= _ ? ->; rewrite unitL=>_.
ssl_dealloc.
ssl_dealloc.
ssl_emp.

Qed.
