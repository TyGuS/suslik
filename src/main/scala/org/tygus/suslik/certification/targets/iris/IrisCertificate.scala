package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.targets.iris.heaplang.Expressions.HFunDef
import org.tygus.suslik.certification.targets.iris.logic.Assertions.IFunSpec
import org.tygus.suslik.certification.{Certificate, CertificateOutput, CertificationTarget}

case class IrisCertificate(name: String, funDef: HFunDef, funSpec: IFunSpec) extends Certificate {
  val target: CertificationTarget = Iris

  private val prelude =
    s"""From iris.program_logic Require Export weakestpre.
       |From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
       |From iris.heap_lang Require Import lang notation proofmode.
       |From Hammer Require Import Hammer.
       |Context `{!heapG Σ}.
       |Context {PROP : bi}.
       |Implicit Types Δ : envs PROP.
       |Set Default Proof Using "Type".
       |
       |Definition loc_at x lx := x = LitV (LitLoc lx).
       |Definition int_at x vx := x = LitV (LitInt vx).
       |
       |(* This is a less clever version of tac_and_destruct, which
       |   does NOT break ↦ assertions into fractional assertions. *)
       |Lemma tac_sep_destruct Δ i j1 j2 P P1 P2 Q :
       |  envs_lookup i Δ = Some (false, P) →
       |  (P -∗ P1 ∗ P2) →
       |  match envs_simple_replace i false (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ with
       |  | None => False
       |  | Some Δ' => envs_entails Δ' Q
       |  end →
       |  envs_entails Δ Q.
       |Proof.
       |  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
       |  rewrite envs_entails_eq. intros H0 H1 H2. rewrite envs_simple_replace_sound //=.
       |  by rewrite /= right_id -(comm _ P1) H2 -H1 bi.wand_elim_r.
       |Qed.
       |
       |Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
       |  eapply tac_sep_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
       |    [pm_reflexivity
       |    |pm_reduce; iSolveTC
       |    |pm_reduce;
       |     lazymatch goal with
       |       | |- False => fail
       |       | _ => idtac
       |     end].
       |
       |Local Ltac iSplitAllHyps :=
       |  iStartProof;
       |  let rec go Hs :=
       |      match Hs with [] => idtac | ?H :: ?Hs =>
       |        let Hn := iFresh in
       |        try iAndDestruct H as H Hn; go Hs end in
       |  match goal with
       |  | |- envs_entails ?Δ _ =>
       |     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
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
       |  | [H: loc_at _ _ |- _ ] => rewrite H
       |  | [H: int_at _ _ |- _ ] => rewrite H
       |  | [H: bool_decide _  = _ |- _ ] => rewrite H
       |  end.
       |
       |Local Ltac iSimplContext :=
       |  wp_pures; iSplitAllHyps; iRewriteHyp; iSimpl in "# ∗"; iSimpl.
       |
       |Ltac ssl_begin := iIntros; (wp_rec; repeat wp_let); iSimplContext.
       |Ltac ssl_load := wp_load; wp_let.
       |Ltac ssl_store := wp_store.
       |Ltac ssl_finish := by iFindApply; iFrame "% # ∗".
       |
       |""".stripMargin

  def pp : String = {
    val b = new StringBuilder
    b.append(prelude)
    b.append(funDef.pp)
    b.append("\n")
    b.append(funSpec.pp)
    b.append("Proof.\nAdmitted.\n")
    b.toString()
  }

  override def outputs: List[CertificateOutput] =  List(CertificateOutput(None, name, pp))
}
