From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

(* PREDICATES *)

(*

predicate rose_tree(loc x) {
|  x == 0        => { self_card == 0 ; emp }
|  not (x == 0)  => { z < self_card; [x, 1] ** x :-> b ** buds(b)<z>}
}

predicate buds(loc x) {
|  x == 0        => { self_card == 0 ; emp }
|  not (x == 0)  => { y < self_card /\ z < self_card;
                      [x, 3] ** x :-> v ** (x + 1) :-> r ** rose_tree(r)<y> ** (x + 2) :-> nxt ** buds(nxt)<z> }
}


*)

Inductive rose_tree (x: ptr) (h: heap) : Prop :=
| rose_tree0 of x == null of
                       h = empty
| rose_tree1 of x != null of
             exists b,
               exists h',
                 h = x :-> b \+ h' /\ buds b h'
with buds (x: ptr) (h: heap) : Prop :=
| buds0 of x == null of
                  h = empty
| buds1 of x != null of
        exists (v: nat) r nxt,
        exists h' h'',
          h = x :-> v \+ x .+ 1 :-> r \+ x .+ 2 :-> nxt \+ h' \+ h'' /\ rose_tree r h' /\ buds nxt h''
          
.

(* SPECIFICATION *)

(*
{ rose_tree(x)<a> }
  void rose_tree_free(loc x)
{ emp }

 *)

Definition rose_tree_free_type :=
  forall (x: ptr),
    STsep (
        fun h => rose_tree x h,
        [vfun (_: unit) h => h = empty]).

Definition rose_tree_free10_type :=
  forall (x: ptr),
    STsep (
        fun h => rose_tree x h,
        [vfun (_: unit) h => h = empty]).

(* PROGRAM *)

(*

void rose_tree_free (loc x) {
  if (x == 0) {
  } else {
    rose_tree_free10(x);
  }
}
    
void rose_tree_free10 (loc x) {
  let b = *x;
  if (b == 0) {
    free(x);
  } else {
    let r = *(b + 1);
    let n = *(b + 2);
    rose_tree_free(r);
    *x = n;
    rose_tree_free10(x);
    free(b);
  }
}

*)

Program Definition rose_tree_free : rose_tree_free_type :=
  Fix (fun (rose_tree_free : rose_tree_free_type) x =>
    Do (
        let: rose_tree_free10 :=
           Fix (fun (rose_tree_free10: rose_tree_free_type) (x: ptr) =>
             Do (
               b <-- @read ptr x;
               if b == 0
               then
                 dealloc x;;
                 dealloc (x .+ 1);;
                 dealloc (x .+ 2)
               else
                 r <-- @read ptr (b .+ 1);
                 n <-- @read nat (b .+ 2);
                 rose_tree_free r;;
                 x ::= n;;
                 rose_tree_free10 x;;
                 dealloc b;;
                 dealloc (b .+ 1);;
                 dealloc (b .+ 2)
               ))
        in
        if x == 0 then ret tt else rose_tree_free10 x)).
             
                                                  
