Require Export Utf8.
Require Export PeanoNat.
Require Export Nat.
Require Export List.
Require Export Tapl.Data.List.

(* Reflexive/transitive closure of a relation *)
Inductive multi_rel {A} (r : A → A → Prop) : A → A → Prop :=
  | multi_refl  : ∀ (a : A), 
      multi_rel r a a
  | multi_trans : ∀ (a b c : A),
      r a b →
      multi_rel r b c →
      multi_rel r a b.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.
