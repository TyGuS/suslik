From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition min2_type :=
  forall (r : ptr) (x : nat) (y : nat),
    STsep (
      fun h =>
          h = r :-> 0,
      [vfun (_: unit) h =>
        exists m,
          m <= x /\ m <= y /\ h = r :-> m      ]).

Program Definition min2 : min2_type :=
  fun r x y =>
    Do (
        if x <= y
        then r ::= x;;
             ret tt
        else r ::= y;;
             ret tt).
Next Obligation.
  ssl_ghostelim_pre.
  move=> ->.
  case: ifP=>Hcond.
  - ssl_write.
    apply: val_ret=>*//=; exists x; hhauto.
  - ssl_write.              
    apply: val_ret=>*//=; exists y; hhauto.
    case: ltngtP Hcond; auto.
Qed.

Definition max_type :=
  forall (r : ptr) (x : nat) (y : nat),
    STsep (
      fun h =>
          h = r :-> 0,
      [vfun (_: unit) h =>
        exists m,
          x <= m /\ y <= m /\ h = r :-> m      ]).
Program Definition max : max_type :=
  fun r x y =>
    Do (
  if y <= x
  then
    r ::= x;;
    ret tt
  else
    r ::= y;;
    ret tt
    ).
Next Obligation.
  (* move precondition heap to context *)
  move=>h//=.
  move=> ->.
  case: ifP=>Hcond.
  - ssl_write.
    apply: val_ret=>*//=; exists x; hhauto.
  - ssl_write.              
    apply: val_ret=>*//=; exists y; hhauto.
    case: ltngtP Hcond; auto.
Qed.


