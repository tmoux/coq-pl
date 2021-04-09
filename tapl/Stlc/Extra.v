Require Import Tapl.Stlc.Base.
Require Import Tapl.Stlc.Exp.
Require Import Tapl.Stlc.Typing.


(* Lemmas *)

(* Lifting a wf term does nothing. *)
Lemma lift_wf_id : forall G t i,
  length G <= i 
  -> wf G t 
  -> lift i t = t.
Proof.
  intros.
  generalize dependent G.
  generalize dependent i.
  induction t; intros; simpl.
  - inversion H0; subst. destruct H3.
    assert (n < length G). apply get_length with (x := x); auto. 
    assert (n < i). { apply Nat.le_trans with (m := length G); auto. }
    destruct (n ?= i) eqn:eqH.
    + apply Nat.compare_eq in eqH. apply Nat.lt_neq in H3. apply H3 in eqH. exfalso; assumption.
    + reflexivity.
    + apply Nat.compare_gt_iff in eqH. apply Nat.lt_asymm in eqH. apply eqH in H3; exfalso; assumption.
  - inversion H0; subst. pose proof IHt (S i) (t :: G).
    assert (lift (S i) t0 = t0).
    apply H1. simpl. apply Le.le_n_S; auto.
    apply H3.
    rewrite H2. reflexivity.
  - inversion H0; subst. apply IHt1 with (i := i) in H4. apply IHt2 with (i := i) in H5. simpl. rewrite -> H4. rewrite -> H5. reflexivity. auto. auto.
  - reflexivity.
Qed.
(* Corollary: lifting closed term does nothing. *)
Lemma lift_closed_id : forall t i,
  closed t -> lift i t = t.
Proof.
  intros. apply lift_wf_id with (G := nil); auto. apply le_0_n.
Qed.
