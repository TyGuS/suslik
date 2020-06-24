From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition swap2_type :=
  forall (x : ptr) (z : ptr) (y : ptr) (t : ptr),
  {(a : nat) (b : nat) (q : nat) (c : nat)},
    STsep (
      fun h =>
          h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
      [vfun (_: unit) h =>
          h = x :-> q \+ z :-> c \+ t :-> a \+ y :-> b      ]).
Program Definition swap2 : swap2_type :=
  fun x z y t =>
    Do (
  a2 <-- @read nat x;
  c2 <-- @read nat y;
  b2 <-- @read nat z;
  q2 <-- @read nat t;
  x ::= q2;;
  y ::= b2;;
  z ::= c2;;
  t ::= a2;;
  ret tt    ).
Next Obligation.
ssl_ghostelim_pre.
move=>[q [a [b c]]]//=.
move=>-> HValid.
ssl_read.
ssl_read.
ssl_read.
ssl_read.
ssl_write.
ssl_write_post x.
ssl_write.
ssl_write_post y.
ssl_write.
ssl_write_post z.
ssl_write.
ssl_write_post t.
ssl_emp.

Qed.
