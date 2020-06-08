From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree0 of x == 0 of
    s = nil /\ h = empty
| tree1 of x != 0 of
  exists v s1 s2 r l,
  exists h' h'',
    s = [:: v] ++ s1 ++ s2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h' \+ h'' /\ tree l s1 h' /\ tree r s2 h''
.
Definition treefree_type :=
  forall (x : ptr),
  {(s : seq nat)},
    STsep (
      fun h =>
          tree x s h,
      [vfun (_: unit) h =>
          h = empty      ]).
Program Definition treefree : treefree_type :=
  Fix (fun (treefree : treefree_type) x =>
    Do (
  if x == 0
  then
    ret tt
  else
    l2 <-- @read ptr (x .+ 1);
    r2 <-- @read ptr (x .+ 2);
    treefree l2;;
    treefree r2;;
    dealloc (x .+ 2);;
    dealloc (x .+ 1);;
    dealloc x;;
    ret tt
    )).
Next Obligation.
ssl_ghostelim_pre.
move=>s//=.
move=>H_tree HValid.
case: ifP=>cond; case H_tree; rewrite cond//==>_.
move=>[E].
move=>[->].

ssl_emp.

move=>[v] [s1] [s2] [r] [l].
move=>[h'] [h''].
move=>[E].
move=>[->].
move=>[H_rec_tree H_rec_tree'].

ssl_read.
ssl_read.
put_to_head h'.
apply: bnd_seq.
apply: (gh_ex s1).

apply: val_do=>//= _ ? ->; rewrite unitL=>_.
put_to_head h''.
apply: bnd_seq.
apply: (gh_ex s2).

apply: val_do=>//= _ ? ->; rewrite unitL=>_.
ssl_dealloc.
ssl_dealloc.
ssl_dealloc.
ssl_emp.

Qed.
