From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition swap1_type :=
  forall (x : ptr) (z : ptr) (y : ptr) (t : ptr),
  {(a : nat) (b : nat) (q : nat) (c : nat)},
    STsep (
      fun h =>
          h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
      [vfun (_: unit) h =>
          h = x :-> c \+ z :-> b \+ t :-> q \+ y :-> 41      ]).
Program Definition swap1 : swap1_type :=
  fun x z y t =>
    Do (
  c2 <-- @read nat y;
  x ::= c2;;
  y ::= 41;;
  ret tt    ).
Next Obligation.
ssl_ghostelim_pre.
move=>[q [a [b c]]]//=.
move=>-> HValid.
ssl_read.
ssl_write.
ssl_write_post x.
ssl_write.
ssl_write_post y.
ssl_emp.

Qed.
