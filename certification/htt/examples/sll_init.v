From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Lemma subset_singleton :
    forall (s1: seq nat) (x: nat),
      {subset s1 <= [::x]} -> {subset x :: s1 <= [::x]}.
intros.
move=>n.
rewrite inE; move/orP. case.
move/eqP=>->. by rewrite inE eqxx.
move/H=>//.
Qed.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll0 of x == 0 of
    s = nil /\ h = empty
| sll1 of x != 0 of
  exists nxt s1 v,
  exists h',
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h' /\ sll nxt s1 h'
.

Definition sll_init_type :=
  forall (arg: ptr * nat),
    {(s : seq nat)},
    STsep (
      fun h =>
       let: (a, b) := arg in
        sll a s h,
        [vfun (_: unit) h =>
                let: (a, b) := arg in

       exists s1,
          {subset s1 <= [:: b]} /\ sll a s1 h      ]).

Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) arg =>
         let: (a, b) := arg in
         Do (
             if a == 0
             then ret tt
             else
               n <-- @read ptr (a .+ 1);
               sll_init (n, b);;
               a ::= b;;
               ret tt
   )).
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
exists nil.
ssl_emp_post.
constructor 1=>//.

case H_sll; rewrite H_cond=>//= _.
move=>[nxt] [s1] [v].
move=>[h'].
move=>[sll_phi].
move=>[->].
move=>H_sll0.
ssl_read.
put_to_head h'.
apply: bnd_seq.
apply: (gh_ex s1).
apply: val_do=>//= _ h''.
move=>[s2] [H_subseq H_sll1].
move=>H_valid0.

ssl_write.
ssl_write_post p.

ssl_emp.
move:H_valid2. rewrite joinC joinA. rewrite defPtUnO; case/andP. move=> H_pnotnull _.
exists (n :: s2).
split=>//=.
apply: subset_singleton=>//.
  
constructor 2=>//=.
exists nxt.
exists s2, n.
exists h''.
ssl_emp_post.
Qed.
