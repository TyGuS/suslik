From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition swap_type :=
  forall (x : ptr) (y : ptr),
  {(a : nat) (b : nat)},
    STsep (
      fun h =>
          h = x :-> a \+ y :-> b,
      [vfun (_: unit) h =>
          h = x :-> b \+ y :-> a      ]).
Program Definition swap : swap_type :=
  fun x y =>
    Do (
  a2 <-- @read nat x;
  b2 <-- @read nat y;
  x ::= b2;;
  y ::= a2;;
  ret tt    ).
Next Obligation.
ssl_ghostelim_pre.
move=>[a b]//=.
move=>-> HValid.
ssl_read.
ssl_read.
ssl_write.
ssl_write_post x.
ssl_write.
ssl_write_post y.
ssl_emp.

Qed.
