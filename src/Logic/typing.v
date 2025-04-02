From MyProject.src.Logic Require Export SysF.
From iris.prelude Require Import options.
From stdpp Require Export base gmap.


Module typing.
(* interesting. since they use autosubst.. 
forall and exists dont hold types, they hold
variables of type*)
Inductive type :=
  | TUnit : type
  | TInt : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExist (τ : {bind 1 of type}).

Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.


(* what is this ?*)
Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TInt
  | EqTBool : EqType TBool.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Import SysF.
(* note that gamma here is really a type environment *)
Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Bool_typed b : Γ ⊢ₜ Bool b : TBool
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 →
     Γ ⊢ₜ e2 : τ2 →
     Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2

  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Lam_typed e τ1 τ2 :
      τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2

  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  (* Here are the interesting cases ..
     autosubst is used again .. which wtf..how?
  *)
  | TLam_typed e τ :
     subst (ren (+1)) <$> Γ ⊢ₜ e : τ → 
     Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : 
    Γ ⊢ₜ e : TForall τ → 
    Γ ⊢ₜ TApp e : τ.[τ'/]
  | Pack_typed e τ τ' :
     Γ ⊢ₜ e : τ.[τ'/] → 
     Γ ⊢ₜ Pack e : TExist τ
  | UnpackIn_typed e1 e2 τ τ' :
     Γ ⊢ₜ e1 : TExist τ →
     τ :: (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] →
     Γ ⊢ₜ UnpackIn e1 e2 : τ'
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).


Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end.


Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x as [|x IH] => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    apply IH.
Qed.


End typing.