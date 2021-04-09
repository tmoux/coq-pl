Require Import Tapl.LambdaSub.Base.
Require Import Tapl.LambdaSub.Exp.

(* Typing *)
Reserved Notation "S '<:' T" (at level 40).
Inductive subtype : type → type → Prop :=
  | S_Refl : ∀ S, S <: S
  | S_Trans : ∀ S U T, 
      S <: U →
      U <: T →
      S <: T
  | S_Top : ∀ T, T <: ty_top
  | S_Arrow : ∀ S1 S2 T1 T2,
      T1 <: S1 →
      S2 <: T2 →
      (ty_arrow S1 S2) <: (ty_arrow T1 T2)
where "S '<:' T" := (subtype S T).
Global Hint Constructors subtype : core.

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
  | Ty_Sub : forall G t S T,
      G ⊢ t ∈ S →
      S <: T →
      G ⊢ t ∈ T
where "G '⊢' t '∈' T" := (has_type G t T). 
Global Hint Constructors has_type : core.

Example ex_ty1 : nil ⊢ tm_abs ty_unit 0 ∈ ty_arrow ty_unit ty_unit.
Proof. auto. Qed.
Example ex_ty2 : (ty_arrow ty_unit ty_unit :: nil) ⊢ tm_app (tm_var 0) tm_unit ∈ ty_unit.
Proof with auto. 
  eapply Ty_App... auto. Qed.

Example ex_sub1 : (ty_arrow ty_top ty_unit) <: (ty_arrow ty_unit ty_top).
Proof. auto. Qed.
(* Inversion lemmas *)
Lemma inversion_unit : ∀ T,
  T <: ty_unit →
  T = ty_unit.
Proof.
  intros T H. 
  remember ty_unit as S.
  induction H; subst; try discriminate; auto.
  - assert (U = ty_unit). auto.
    apply IHsubtype1 in H1. subst. auto.
Qed.

Lemma inversion_arrow : ∀ S T1 T2,
  S <: ty_arrow T1 T2 →
  exists S1 S2, (S = ty_arrow S1 S2 ∧ T1 <: S1 ∧ S2 <: T2).
Proof.
  intros.
  remember (ty_arrow T1 T2) as T.
  generalize dependent T2.
  generalize dependent T1.
  induction H; intros; subst; try discriminate.
  - exists T1; exists T2. auto.
  - pose proof (IHsubtype2 T1 T2 eq_refl).
    destruct H1 as [S1 [S2 [H1 [H2 H3]]]].
    pose proof (IHsubtype1 S1 S2 H1).
    destruct H4 as [S3 [S4 [H4 [H5 H6]]]].
    subst. exists S3; exists S4. split; auto.
    split. apply S_Trans with S1; auto.
    apply S_Trans with S2; auto.
  - inversion HeqT; subst. exists S1; exists S2.
    repeat (split; auto).
Qed.
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

(* Canonical forms *)
Lemma canonical_forms_unit : forall Γ v,
  Γ ⊢ v ∈ ty_unit ->
  value v ->
  v = tm_unit.
Proof with eauto.
  intros.
  remember ty_unit as T.
  induction H; try solve_by_inverts 2...
  - subst. apply IHhas_type... apply inversion_unit...
Qed.

Lemma canonical_forms_arrow : forall Γ v T1 T2,
  Γ ⊢ v ∈ ty_arrow T1 T2 ->
  value v ->
  exists S t, v = tm_abs S t.
Proof with eauto.
  intros.
  remember (ty_arrow T1 T2) as T.
  generalize dependent T2.
  generalize dependent T1.
  induction H; intros; subst; try solve_by_inverts 2...
  - apply inversion_arrow in H1 as [S1 [S2 [H1 [H2 H3]]]].
    eapply IHhas_type... 
Qed.
