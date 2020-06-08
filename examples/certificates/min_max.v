From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* SuSLik bindings *)
Notation empty := Unit.
Local Coercion ptr_nat : nat >-> ptr.
Definition skip := ret tt.

Ltac put_to_head h :=
  (* make everything left associative*)
  repeat match goal with
         | [|- context[?X \+ (?Y \+ ?Z)]] => rewrite -(joinA X Y Z)
         end;
  (* bring to head *)
  match goal with
  | [|- context[?X \+ h]] => rewrite (joinC _ h)
  end;
  (* make the remainder left associative*)
  repeat match goal with
         | [|- context[h \+ ?Y \+ ?Z]] => rewrite -(joinA h Y Z)
         end.

Ltac ssl_read_pre x :=
  match goal with
  | [|- context[x :-> ?V]] => put_to_head (x :-> ?V)
  end.

Ltac ssl_read := apply: bnd_readR=>/=.

Ltac ssl_write := apply: bnd_writeR=>/=.

Ltac ssl_write_post x :=
  rewrite -?joinA;
  match goal with
  | [ |- verify (x :-> _ \+ _) _ _ ] =>
    rewrite ?(joinC (x :-> _))
  | [ |- verify (x :-> _)  _ _ ] =>
    rewrite -(unitL (x :-> _))
  end;
  rewrite ?joinA;
  apply frame.

Ltac ssl_dealloc :=
  apply: bnd_seq;
  match goal with
  | [|- context[_ :-> _ \+ _]] =>
    apply: val_dealloc=>//=_
  | [|- context[_ :-> _]] =>
    apply: val_deallocR=>//=_
  end;
  try match goal with
  | [|- context[_ \+ empty]] =>
    rewrite unitR
  end
.

Ltac ssl_emp := apply: val_ret=>*//=; hhauto.

Ltac ssl_ghostelim_pre := try apply: ghR; move=>h.

Ltac ssl_ghostelim_post := move=>->Vh.

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


