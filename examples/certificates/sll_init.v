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

