Require Import Tapl.LambdaSub.Base.
Require Import Tapl.LambdaSub.Exp.
Require Import Tapl.LambdaSub.Typing.

(* Weakening lemma *)
Lemma type_insert_weaken : ∀ Γ i t T S,
  Γ ⊢ t ∈ T →
  (insert i S Γ) ⊢ (lift i t) ∈ T.
Proof with eauto.
  intros.
  generalize dependent i.
  induction H; intros; simpl...
  - destruct (i ?= i0) eqn:eqH.
    + apply Nat.compare_eq in eqH. rewrite <- eqH. apply Ty_Var. apply insert_shift...
    + apply Nat.compare_lt_iff in eqH. apply Ty_Var. apply insert_noshift...
    + apply Nat.compare_gt_iff in eqH. apply Ty_Var. apply insert_shift... apply Nat.lt_le_incl...
  - apply Ty_Abs. rewrite insert_rewind...
Qed.


Lemma weakening : ∀ Γ t T S,
  Γ ⊢ t ∈ T →
  (S :: Γ) ⊢ (lift 0 t) ∈ T.
Proof with eauto.
  intros.
  - assert ((insert 0 S Γ) ⊢ (lift 0 t) ∈ T).
    apply type_insert_weaken... simpl in H0... destruct Γ...
Qed.

Lemma subst_preserves_typing' : ∀ Γ S T s t i,
  get i Γ = Some S → 
  Γ ⊢ t ∈ T →
  (delete i Γ) ⊢ s ∈ S →
  (delete i Γ) ⊢ substX i s t ∈ T.
Proof with eauto.
  intros.
  generalize dependent s. generalize dependent S. generalize dependent i.
  induction H0; intros; subst...
  - rename i0 into j. 
    destruct (i ?= j) eqn:eqH; simpl; rewrite eqH. 
    + apply Nat.compare_eq in eqH. subst. rewrite H in H0. inversion H0. subst; auto.
    + apply Nat.compare_lt_iff in eqH. constructor. apply delete_lt...
    + apply Nat.compare_gt_iff in eqH. constructor. destruct i. 
      * apply Nat.nlt_0_r in eqH. exfalso... 
      * simpl. apply delete_gt...
  - simpl. constructor. rewrite delete_rewind. eapply IHhas_type. simpl. apply H. simpl. apply weakening...
  - simpl. eauto.
Qed.

(* Substitution lemma *)
Lemma subst_preserves_typing : forall Γ S T s t,
    (S :: Γ) ⊢ t ∈ T ->
    Γ ⊢ s ∈ S ->
    Γ ⊢ substX 0 s t ∈ T.
Proof with eauto.
  intros. assert (delete 0 (S :: Γ) ⊢ (substX 0 s t) ∈ T)...
  apply subst_preserves_typing' with S...
Qed.

(* Example of substitution *)
Module SubstTest.
Parameter S T : type.
Definition Γ := T :: nil.
Definition s := tm_abs T (tm_var 1).
Definition t := tm_app (tm_var 1) (tm_var 2).
Lemma t_type : (S :: (ty_arrow T T) :: Γ) ⊢ t ∈ T.
Proof. unfold t. apply Ty_App with T; auto. Qed.
Lemma s_type : Γ ⊢ s ∈ ty_arrow T T.
Proof. unfold s. auto. Qed.
Lemma subst_st : (S :: Γ) ⊢ substX 1 (lift 0 s) t ∈ T.
Proof. simpl. eauto. Qed.

Lemma subst_st_wrong : (S :: Γ) ⊢ substX 1 s t ∈ T.
Proof. simpl. unfold s. eauto. Abort.

End SubstTest.


