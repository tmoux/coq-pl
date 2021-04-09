Require Import Tapl.DSub.Base.


Inductive type : Set :=
  | ty_top  : type (* ⊤ *)
  | ty_bot  : type (* ⊥ *)
  | ty_decl : type → type → type (* {A : S .. T *)
  | ty_proj : nat → type (* x.A *)
  | ty_dep_fun : type → type → type. (* ∀(x:S) T *)

Inductive term : Set :=
  | tm_var : nat → term
  | tm_tag : type → term
  | tm_abs : type → term → term
  | tm_app : term → term → term
  | tm_let : term → type → term → term.

Definition context := list type.
Inductive wfT : context → type → Prop := 
  | wfT_top : ∀ Γ, wfT Γ ty_top
  | wfT_bot : ∀ Γ, wfT Γ ty_bot
  | wfT_decl : ∀ Γ S T,
      wfT Γ S → wfT Γ T →
      wfT Γ (ty_decl S T)
  | wfT_proj : ∀ Γ i,
      (∃ T, get i Γ = Some T) →
      wfT Γ (ty_proj i)
  | wfT_dep_fun : ∀ Γ S T,
      wfT Γ S →
      wfT (S :: Γ) T →
      wfT Γ (ty_dep_fun S T)
.

Inductive wfX : context → term → Prop :=
  | wfX_var : ∀ Γ i,
      (∃ T, get i Γ = Some T) →
      wfX Γ (tm_var i)
  | wfX_tag : ∀ Γ T,
      wfT Γ T →
      wfX Γ (tm_tag T)
  | wfX_abs : ∀ Γ T t,
      wfT Γ T →
      wfX (T :: Γ) t →
      wfX Γ (tm_abs T t)
  | wfX_app : ∀ Γ t1 t2,
      wfX Γ t1 →
      wfX Γ t2 →
      wfX Γ (tm_app t1 t2)
  | wfX_let : ∀ Γ t1 T t2,
      wfX Γ t1 →
      wfX (T :: Γ) t2 →
      wfX Γ (tm_let t1 T t2).

Definition closed := wfX nil.
