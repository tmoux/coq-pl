Require Import Tapl.Stlc.Base.
Require Import Tapl.Stlc.Exp.
Require Import Tapl.Stlc.Subst.
Require Import Tapl.Stlc.Typing.

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
      * pose proof (canonical_forms_arrow t1 T1 T2 H H1).
        destruct H3 as [t' H3]. subst.
        exists (substX 0 t2 t')...
      * destruct H2 as [t2' H2].
        exists (tm_app t1 t2')...
    + destruct H1 as [t1' H1]. exists (tm_app t1' t2)...
  - (* If ⊢ t was derived from the unit rule, t is a value. *)
    left; split; unfold closed...
Qed.

(* Preservation: If t has type T and steps to t', then t' also has type T. *)
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
    + apply subst_preserves_typing with T1...
      inversion H0_; subst...
  - inversion H.
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
