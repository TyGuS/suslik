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
  exists heap_sll_alpha_513,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ heap_sll_alpha_513 /\ sll nxt s1 heap_sll_alpha_513
.
Definition sll_singleton_type :=
  forall (x : nat) (p : ptr),
  {(a : nat)},
    STsep (
      fun h =>
          h = p :-> a,
      [vfun (_: unit) h =>
        exists y (elems: seq nat),
        exists heap_sll_alpha_514,
          elems = [:: x] /\ h = p :-> y \+ heap_sll_alpha_514 /\ sll y elems heap_sll_alpha_514      ]).
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
ssl_ghostelim_post.
ssl_alloc y2.
ssl_write.
ssl_write_post p.
ssl_write.
ssl_write_post (y2 .+ 1).
ssl_write.
ssl_write_post y2.
ssl_emp;
exists (y2), ([:: x] ++ nil);
exists (y2 :-> x \+ y2 .+ 1 :-> null);
ssl_emp_post.
constructor 2=>//;
exists 0, nil, x;
exists empty;
ssl_emp_post.
constructor 1=>//;
ssl_emp_post.

Qed.
