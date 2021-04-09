Require Import Utf8.
Require Import List. 
Require Import PeanoNat.


Fixpoint get {A : Type} (i : nat) (l : list A): option A :=
  match l, i with
  | x :: _ , O    => Some x
  | _ :: xs, S i' => get i' xs
  | _      , _    => None
  end.

Fixpoint delete {A : Type} (i : nat) (G : list A) :=
  match i, G with
  | _   , nil   => nil
  | O   , x::xs => xs
  | S i', x::xs => x :: delete i' xs
  end.

Fixpoint insert {A : Type} (i : nat) (a : A) (G : list A) :=
  match i, G with
  | _   , nil   => a::nil
  | O   , xs    => a::xs
  | S i', x::xs => x::insert i' a xs
  end.

Fixpoint list_replace {A : Type} (i : nat) (a : A) (G : list A) :=
  match i, G with
  | _   , nil   => nil
  | O   , x::xs => a::xs
  | S i', x::xs => x::list_replace i' a xs
  end.

Lemma get_nil : forall A n (T: A),
  ~(get n nil = Some T).
Proof.
  unfold not; intros.
  destruct n; simpl in *; discriminate.
Qed.

Lemma get_length : forall A (G : list A) n x,
  get n G = Some x -> n < length G.
Proof.
  intros.
  generalize dependent x.
  generalize dependent n.
  induction G; intros; simpl in *.
  - destruct n; simpl in *; discriminate.
  - destruct n; simpl in *. apply Nat.lt_0_succ.
    rewrite <- Nat.succ_lt_mono. apply IHG with x; auto.
Qed.

Lemma delete_rewind : ∀ {A : Type} (Γ : list A) (t : A) i,
  t :: delete i Γ = delete (S i) (t :: Γ).
Proof.
  auto.
Qed.

Lemma insert_rewind : ∀ {A : Type} (Γ : list A) (t : A) i T1 T2,
  T1 :: insert i T2 Γ = insert (S i) T2 (T1 :: Γ).
Proof.
  auto.
Qed.

Lemma delete_lt : forall {A : Type} (Γ : list A) T i n,
  get i Γ = Some T →
  i < n →
  get i (delete n Γ) = Some T.
Proof with eauto.
  intros.
  generalize dependent i. generalize dependent n.
  induction Γ; intros...
  - apply get_length in H. apply Nat.nlt_0_r in H. exfalso...
  - destruct i.
    + simpl in H. simpl. destruct n.
      * apply Nat.nlt_0_r in H0. exfalso...
      * auto.
    + simpl. destruct n.
      * apply Nat.nlt_0_r in H0. exfalso...
      * simpl in *. apply IHΓ... rewrite Nat.succ_lt_mono...
Qed.

Lemma delete_gt : ∀ {A : Type} (Γ : list A) T i n,
  get (S n) Γ = Some T →
  i < S n →
  get n (delete i Γ) = Some T.
Proof with eauto.
  intros.
  generalize dependent i. generalize dependent n.
  induction Γ; intros...
  - inversion H.
  - destruct i; simpl.
    + inversion H...
    + destruct n.
      * inversion H0. inversion H2.
      * simpl. apply IHΓ... rewrite Nat.succ_lt_mono...
Qed.


Lemma insert_shift : ∀ {A : Type} (G : list A) i j t T,
  j <= i →
  get i G = Some T →
  get (S i) (insert j t G) = Some T.
Proof.
  intros.
  generalize dependent i. generalize dependent j.
  induction G; intros.
  - destruct j; simpl; auto. 
  - simpl. destruct j; simpl; auto. 
    destruct i. inversion H.
    assert (get (S i) (a :: G) = get i G). auto.
    apply IHG. apply Nat.succ_le_mono; auto. simpl in H0; auto.
Qed.

Lemma insert_noshift : ∀ {A : Type} (G : list A) i j t T,
  j < i →
  get j G = Some T →
  get j (insert i t G) = Some T.
Proof with eauto.
  intros.
  generalize dependent j.
  generalize dependent G.
  induction i; intros...
  - inversion H. 
  - destruct G. apply get_nil in H0. exfalso...
    simpl. destruct j; simpl in *...
    + apply IHi; try apply Nat.succ_lt_mono...
Qed.
