Require Import Tapl.LambdaSub.Base.

(* Our presentation of simply typed lambda calculus has a single base type, Unit. *)
Inductive type : Type :=
  | ty_unit  : type 
  | ty_arrow : type → type → type
  | ty_top   : type.

Inductive term : Type :=
  | tm_var  : nat → term
  | tm_abs  : type → term → term
  | tm_app  : term → term → term
  | tm_unit : term.

Coercion tm_var : nat >-> term.

(* Values *)

Definition context := list type.
Inductive wf : context -> term -> Prop :=
  | wf_var  : forall G i, 
         (exists T, get i G = Some T)
      -> wf G (tm_var i)
  | wf_abs  : forall G T t,
         wf (T :: G) t 
      -> wf G (tm_abs T t)
  | wf_app  : forall G t1 t2,
         wf G t1
      -> wf G t2
      -> wf G (tm_app t1 t2)
  | wf_unit : forall G, 
      wf G tm_unit.
Global Hint Constructors wf : core.

Definition closed (t: term) := wf nil t.

Inductive wnfX : term → Prop :=
  | wnf_val : ∀ T t, wnfX (tm_abs T t)
  | wnf_unit : wnfX tm_unit.
Global Hint Constructors wnfX : core.

Definition value (t : term) := wnfX t ∧ closed t.

(* Substitution *)

(* lift shifts all the free variables over by 1 *)

Fixpoint lift (k : nat) (t : term) :=
  match t with
  | tm_var i => match compare i k with 
                | Lt => tm_var i
                | _  => tm_var (S i)
                end
  | tm_abs T t' => tm_abs T (lift (S k) t')
  | tm_app t1 t2 => tm_app (lift k t1) (lift k t2)
  | tm_unit => tm_unit
  end.

(*
Fixpoint lift (k : nat) (t : term) :=
  match t with
  | tm_var i => if leb k i
                then tm_var (S i)
                else tm_var i
  | tm_abs T t' => tm_abs T (lift (S k) t')
  | tm_app t1 t2 => tm_app (lift k t1) (lift k t2)
  | tm_unit => tm_unit
  end.
*)
(* [k -> s]t *)
(* substX replaces the k'th free variable with s in t.
   if s has free variables, s is lifted when substituting over binders to make sure the free variables in s are correct.
   All free variables j > k are shifted down one, to account for the fact that the k'th free variable has been substituted.
*)
Fixpoint substX (k : nat) (s : term) (t : term) :=
  match t with
  | tm_var i => match compare i k with
                | Eq => s
                | Lt => tm_var i
                | Gt => tm_var (pred i)
                end
  | tm_abs T t' => tm_abs T (substX (S k) (lift 0 s) t')
  | tm_app t1 t2 => tm_app (substX k s t1) (substX k s t2)
  | tm_unit => tm_unit
  end.

(* Examples *)
(* [0 -> (λ.T 0)] (1 0 2) = 0 (λ.T 0) 1*)
Example ex1 : substX 0 (tm_abs ty_unit 0) (tm_app (tm_app 1 0) 2)
            = tm_app (tm_app 0 (tm_abs ty_unit 0)) 1.
Proof.
  simpl. reflexivity.
Qed.




(* Evaluation *)

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : term -> term -> Prop :=
  | st_app1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_app t1 t2 --> tm_app t1' t2
  | st_app2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | st_appAbs : forall T t1 v2,
      value v2 ->
      tm_app (tm_abs T t1) v2 --> substX 0 v2 t1
      
where "t '-->' t'" := (step t t').
Global Hint Constructors step : core.

(* multi_step is the reflexive/transitive closure of the step relation *)

Definition multi_step := multi_rel step.
Notation "t '-->*' t'" := (multi_step t t') (at level 40).
(*
Inductive multi_step : term -> term -> Prop := 
  | ms_refl : forall t, 
      t -->* t
  | ms_trans : forall t1 t2 t3,
      t1 --> t2 ->
      t2 -->* t3 ->
      t1 -->* t3
where "t '-->*' t'" := (multi_step t t').
*)





