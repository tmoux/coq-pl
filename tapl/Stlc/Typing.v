Require Import Tapl.Stlc.Base.
Require Import Tapl.Stlc.Exp.
Require Import Tapl.Data.List.

(* Typing *)
Reserved Notation "G '⊢' t '∈' T" (at level 40).
Inductive has_type : context -> term -> type -> Prop :=
  | Ty_Var : forall G i T,
      get i G = Some T -> 
      G ⊢ tm_var i ∈ T
  | Ty_Abs : forall G t T1 T2,
      (T1 :: G) ⊢ t ∈ T2 ->
      G ⊢ tm_abs T1 t ∈ ty_arrow T1 T2
  | Ty_App : forall G t1 t2 T1 T2,
      G ⊢ t1 ∈ ty_arrow T1 T2 ->
      G ⊢ t2 ∈ T1 ->
      G ⊢ tm_app t1 t2 ∈ T2
  | Ty_Unit : forall G,
      G ⊢ tm_unit ∈ ty_unit
where "G '⊢' t '∈' T" := (has_type G t T). 
Global Hint Constructors has_type : core.

Example ex_ty1 : nil ⊢ tm_abs ty_unit 0 ∈ ty_arrow ty_unit ty_unit.
Proof. auto. Qed.
Example ex_ty2 : (ty_arrow ty_unit ty_unit :: nil) ⊢ tm_app (tm_var 0) tm_unit ∈ ty_unit.
Proof with auto. 
  eapply Ty_App... auto. Qed.

(* Typing implies well-formedness. *)
Lemma typing_implies_wf : forall Γ t T,
  Γ ⊢ t ∈ T →
  wf Γ t.
Proof.
  intros.
  induction H; auto.
  - apply wf_var. exists T; assumption.
Qed.
Global Hint Resolve typing_implies_wf : core.

(* Typing of terms is unique. *)
Lemma typing_unique : forall t G T1 T2,
    G ⊢ t ∈ T1 -> 
    G ⊢ t ∈ T2 ->
    T1 = T2.
Proof with auto.
  intros t.
  induction t; intros; inversion H0; subst; inversion H; subst; simpl...
  - rewrite -> H3 in H4.
    inversion H4; auto.
  - assert (T2 = T3). apply IHt with (t :: G)... subst; auto.
  - assert (T0 = T3). apply IHt2 with G... subst.
    assert (ty_arrow T3 T2 = ty_arrow T3 T1). apply IHt1 with G... inversion H1; subst...
Qed.

(* Canonical forms *)
Lemma canonical_forms_unit : forall v,
  nil ⊢ v ∈ ty_unit ->
  value v ->
  v = tm_unit.
Proof.
  intros.
  destruct H0.
  destruct H0.
  - inversion H.
  - reflexivity.
Qed.

Lemma canonical_forms_arrow : forall v T1 T2,
  nil ⊢ v ∈ ty_arrow T1 T2 ->
  value v ->
  exists t, v = tm_abs T1 t.
Proof.
  intros.
  destruct H0; destruct H0; inversion H; subst.
  - exists t. reflexivity.
Qed.
