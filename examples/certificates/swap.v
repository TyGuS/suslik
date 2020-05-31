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
  match goal with
  | [ |- verify (x :-> _ \+ _) _ _ ] =>
    rewrite !(joinC (x :-> _))
  | [ |- verify (x :-> _)  _ _ ] =>
    rewrite -(unitL (x :-> _))
  end;
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

Ltac ssl_emp := apply: val_ret=>//.

Ltac ssl_ghostelim_pre := apply: ghR; move=>h.

Ltac ssl_ghostelim_post := move=>->Vh.

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