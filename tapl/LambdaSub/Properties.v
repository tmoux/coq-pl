Require Import Tapl.LambdaSub.Base.
Require Import Tapl.LambdaSub.Exp.
Require Import Tapl.LambdaSub.Subst.
Require Import Tapl.LambdaSub.Typing.

(* Progress: Every well-typed term is either a value or can take a step. *)
Theorem progress : forall t T,
    nil ⊢ t ∈ T ->
    value t ∨ exists t', t --> t'.
Proof with auto.
  intros.
  remember nil as G.
  induction H; subst.
  - (* If ⊢ t was derived from the variable rule, this is a contradiction since there are no free variables in the empty context. *)
    exfalso. apply get_nil in H...
  - (* If ⊢ t was derived from the abstraction rule, t is a value, so we're done. *)
    left; split... apply wf_abs. eauto.
  - (* By our inductive hypothesis, t1 is either a value, or it can step to t1'. 
       If it can step, then we just follow st_app1. If it is a value, then t2 is either a value or it can step to t2'. 
       If it can step to t2', then we just follow st_app2. If t2 is a value, then since by the canonical arrow lemma, t1 must be an abstraction, so we can follow st_appAbs. *)
    right.
    pose proof (IHhas_type1 eq_refl).
    pose proof (IHhas_type2 eq_refl).
    destruct H1.
    + destruct H2.
      * pose proof (canonical_forms_arrow nil t1 T1 T2 H H1).
        destruct H3 as [S [t' H3]]. subst.
        exists (substX 0 t2 t')...
      * destruct H2 as [t2' H2].
        exists (tm_app t1 t2')...
    + destruct H1 as [t1' H1]. exists (tm_app t1' t2)...
  - (* If ⊢ t was derived from the unit rule, t is a value. *)
    left; split; unfold closed...
  - apply IHhas_type...
Qed.

(* Preservation: If t has type T and steps to t', then t' also has type T. *)

Lemma typing_inversion_abs : forall Γ S1 t T,
  Γ ⊢ (tm_abs S1 t) ∈ T →
  ∃ S2, ty_arrow S1 S2 <: T ∧ (S1 :: Γ) ⊢ t ∈ S2.
Proof. 
  intros.
  remember (tm_abs S1 t) as s.
  induction H; inversion Heqs; subst; intros; try solve_by_invert.
  - exists T2; auto.
  - destruct IHhas_type as [S2 [Hsub Hty]]. reflexivity.
    exists S2. eauto.
Qed.

Lemma abs_arrow : forall Γ S1 s2 T1 T2,
  Γ ⊢ (tm_abs S1 s2) ∈ ty_arrow T1 T2 →
  T1 <: S1 ∧ (S1 :: Γ) ⊢ s2 ∈ T2.
Proof.
  intros.
  apply typing_inversion_abs in H.
  destruct H as [S2 [H1 H2]].
  apply inversion_arrow in H1 as [S3 [S4 [H3 [H4 H5]]]]. 
  inversion H3; subst. eauto.
Qed.

Theorem preservation : forall t t' T,
    t --> t' ->
    nil ⊢ t ∈ T ->
    nil ⊢ t' ∈ T.
Proof with eauto.
  intros.
  generalize dependent t'.
  remember nil as Γ.
  induction H0; intros; subst.
  - exfalso. apply get_nil in H...
  - inversion H.
  - inversion H; subst...
    + assert (H' := H0_).
      apply abs_arrow in H0_ as [HT1 HT2].
      eapply subst_preserves_typing with T...
  - inversion H.
  - apply Ty_Sub with S...
Qed.

(* Type safety: If t has type T, then it never reaches a stuck state. *)
Definition stuck (t : term) := ¬ value t ∧ ¬ exists t', t --> t'.

Theorem soundness : ∀ t t' T,
  nil ⊢ t ∈ T →
  t -->* t' →
  ¬ (stuck t).
Proof with eauto.
  intros.
  unfold stuck.
  induction H0; unfold not; intros [HA HB].
  - apply progress in H. destruct H as [vt | [t' Ht]]...
  - apply (preservation a b T) in H...
Qed.
