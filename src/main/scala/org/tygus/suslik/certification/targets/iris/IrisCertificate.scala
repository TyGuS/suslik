package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.logic.Assertions.{IFunSpec, IPredicate}
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget, CoqOutput}

case class IrisCertificate(name: String, predicates: List[IPredicate], funDef: HFunDef, funSpec: IFunSpec, proofStr: String) extends Certificate[Iris, IPredicate] {
  val target: CertificationTarget = Iris()

  private val prelude =
    s"""From iris.program_logic Require Export weakestpre.
       |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
       |From iris.heap_lang Require Import lang notation proofmode.
       |From iris_string_ident Require Import ltac2_string_ident.
       |
       |From Hammer Require Import Hammer.
       |Context `{!heapG Σ}.
       |Set Default Proof Using "Type".
       |
       |Definition null_loc : loc := {|loc_car := 0 |}.
       |
       |Axiom NilNotLval:
       |  forall x v,
       |  x ↦ v -∗ x ↦ v ∗ ⌜x ≠ null_loc⌝.
       |
       |Remove Hints fractional.into_sep_fractional fractional.into_sep_fractional_half : typeclass_instances.
       |
       |(* This is exactly iAndDestruct in ltac_tactics.v, which is not exported. *)
       |Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
       |  eapply tac_and_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
       |    [pm_reflexivity
       |    |pm_reduce; iSolveTC
       |    |pm_reduce;
       |     lazymatch goal with
       |       | |- False => fail
       |       | _ => idtac
       |     end].
       |
       |Local Ltac movePure :=
       |  iStartProof;
       |  let rec go Hs := match Hs with [] => idtac | ?H :: ?Hs => (try iDestruct H as "%"); go Hs end in
       |  match goal with
       |  | |- envs_entails ?Δ _ =>
       |    let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
       |  end.
       |
       |Local Ltac iSplitAllHyps :=
       |  iStartProof;
       |  let rec go Hs success :=
       |      match Hs with
       |        [] => match success with | true => idtac | false => fail end
       |      | ?H :: ?Hs => let Hn := iFresh in (iAndDestruct H as H Hn; go Hs true)  || go Hs success
       |      end in
       |  repeat match goal with
       |  | |- envs_entails ?Δ _ =>
       |    let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs false
       |  end;
       |  repeat match goal with
       |  | [H: _ /\\ _ |- _ ] => destruct H
       |  end.
       |
       |Local Ltac iFindApply :=
       |  iStartProof;
       |  let rec go Hs :=
       |      match Hs with [] => idtac | ?H :: ?Hs =>
       |        try iApply H; go Hs end in
       |  match goal with
       |  | |- envs_entails ?Δ _ =>
       |     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
       |  end.
       |
       |Local Ltac iRewriteHyp :=
       |  repeat match goal with
       |  | [H: bool_decide _  = _ |- _ ] => rewrite H
       |  | [H : _ = _ |- _ ]=> rewrite H
       |  end.
       |
       |Local Ltac iSimplNoSplit :=
       |  (repeat wp_pures); movePure; iRewriteHyp. (* iSimpl in "# ∗"; iSimpl. *)
       |
       |Local Ltac iSimplContext := iSimplNoSplit; try iSplitAllHyps; iSimplNoSplit.
       |Ltac dispatchPure := iRewriteHyp; try lia; try sauto; done.
       |
       |Ltac safeDispatchPure :=
       |lazymatch goal with
       || [ |- (envs_entails _) _ ]  => idtac
       || _ => by dispatchPure
       |end.
       |
       |Ltac ssl_begin := (wp_rec; repeat wp_let); iSimplContext.
       |Ltac ssl_let := wp_let.
       |Ltac ssl_load := wp_load; wp_let; iSimplContext.
       |Ltac ssl_store := wp_store; iSimplContext.
       |Ltac ssl_free := wp_free; wp_pures; iSimplContext.
       |Ltac ssl_if H := case_bool_decide as H; wp_if; iSimplContext.
       |Ltac ssl_finish := iRewriteHyp; iFrame "# ∗"; try (try iPureIntro; try safeDispatchPure).
       |
       |Ltac ssl_rewrite_term H term :=
       |let Htn := fresh in let Heqn := fresh in
       |remember term as Htn eqn:Heqn in * at 1;
       |rewrite H in Heqn; rewrite Heqn; clear Htn Heqn.
       |
       |Ltac ssl_apply_to_heap tac :=
       |match goal with
       || [ |- _ (_ ?H) ] => tac H
       |end.
       |
       |Ltac apply_first_heap H tac :=
       |  match H with
       |  | (?A ∗ ?B)%I => apply_first_heap A tac
       |  | (?A ∗ ?B)%I => tac A
       |  | (?A ∗ ?B)%I => apply_first_heap B tac
       |  | (?A ∗ ?B)%I => tac B
       |  | _ => fail "apply_last_heap failed on: "H
       |  end.
       |
       |Ltac pull_out_exist_internal H :=
       | lazymatch H with
       | | ((bi_exist _) ∗ _)%I => rewrite bi.sep_exist_r
       | | (_ ∗ (bi_exist ?Q))%I => rewrite bi.sep_exist_l
       | | (?A ∗ ?B)%I => pull_out_exist_internal A || pull_out_exist_internal B
       | | _ => fail
       | end.
       |
       |Ltac pull_out_exist := repeat ssl_apply_to_heap ltac:(fun H => pull_out_exist_internal H).
       |
       |Ltac sll_rewrite_first_heap lemma :=
       |  ssl_apply_to_heap ltac:(fun H => apply_first_heap H
       |        ltac:(fun H1 => ssl_rewrite_term lemma H1) || ssl_rewrite_term lemma H).
       |
       |Ltac tac_except_post tac :=
       |  lazymatch goal with
       |  | |- envs_entails ?Δ _ =>
       |    let Hs := pm_eval (env_lookup (INamed "Post") (env_spatial Δ)) in
       |    let f := fresh in let feqn := fresh in
       |    lazymatch Hs with
       |    | Some((_ ?H) _) => remember H as f eqn:feqn; tac; (rewrite feqn; clear f feqn)
       |    end
       |  end.
       |
       |""".stripMargin

  def pp : String = {
    val b = new StringBuilder
    b.append(prelude)
    b.append(predicates.map(_.pp).mkString("\n"))
    b.append("\n")
    b.append(predicates.flatMap(_.getHelpers).map(_.pp).mkString("\n"))
    b.append(funDef.pp)
    b.append("\n")
    b.append(funSpec.pp)
    b.append("Proof.\n")
    b.append(proofStr)
    b.append("Qed.\n")
    b.toString()
  }

  override def outputs: List[CertificateOutput] =  List(CoqOutput(s"$name.v", name, pp))
}
