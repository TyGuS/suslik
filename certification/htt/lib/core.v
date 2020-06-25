From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.

(* SuSLik bindings *)
Notation empty := Unit.
Coercion ptr_nat : nat >-> ptr.
Definition skip := ret tt.

Ltac put_to_tail_ptr p :=
  rewrite -?joinA; rewrite ?(joinC (p :-> _) _); rewrite ?joinA.

Ltac put_to_tail h :=
  rewrite -?joinA; rewrite ?(joinC h _); rewrite ?joinA.

Ltac put_to_head h :=
  put_to_tail h;
  rewrite (joinC _ h).

Ltac ssl_read := apply: bnd_readR=>/=.

Ltac ssl_write := apply: bnd_writeR=>/=.

Ltac ssl_write_post x :=
  (put_to_tail_ptr x + rewrite -(unitL (x :-> _))); apply frame.

Ltac ssl_alloc x :=
  apply: bnd_allocbR=>x//=.

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

Ltac non_null :=
  rewrite defPtUnO;
  case/andP;
  let not_null := fresh "not_null" in move=>not_null;
  case/andP;
  rewrite ?unitL;
  match goal with
  | [|- context[valid empty] ] =>
    repeat match goal with
           | [|- _ -> _] => move=>_
           end
  | _ => non_null
  end.

Ltac store_valid_hyps :=
  match goal with
  | [|- _ ->  _ -> _ ] =>
    let hyp := fresh "H_valid" in move=>hyp;
    store_valid_hyps
  | [|-  _ = _ ->  _ ] =>
    move=>_
  | [|-  _ ->  _ ] =>
    let hyp := fresh "H_valid" in move=>hyp;
    try (move:(hyp); non_null)
  end.

Ltac ssl_emp := apply: val_ret; rewrite ?unitL; store_valid_hyps; move=>//.

Ltac ssl_emp_post :=
  repeat match goal with
  | [|- _ /\ _] => split=>//
  | [|- _ = _] => rewrite ?unitL; rewrite ?unitR; hhauto
  | [H_cond: _ |- _] => case: ltngtP H_cond=>//
  end.

Ltac ssl_ghostelim_pre := try apply: ghR; move=>h.

Ltac ssl_ghostelim_post := try store_valid_hyps.

