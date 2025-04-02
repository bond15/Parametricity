From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe.
From stdpp Require Import base gmap.
From iris.prelude Require Import options.
Require Import Autosubst.Autosubst.
From Coq Require Import Unicode.Utf8.
Module OSum.


Inductive type :=
  | TUnit : type
  | TInt : type
  | TBool : type
  | TOSum : type
  | TProd : type → type → type
  | TArrow : type → type → type   
  | TVar (x : var)
  | TCase (τ : {bind type})
  | TForall (τ : {bind type})
  | TExist (τ : {bind type}).


Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.
  Global Instance type_dec_eq (t t' : type) : Decision (t = t').
  Proof. solve_decision. Defined.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Global Instance binop_dec_eq (op op' : binop) : Decision (op = op').
  Proof. solve_decision. Defined.

  Definition loc := positive.

  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l').
    Proof. solve_decision. Defined.

  
  Print Decision.

    Print loc_dec_eq.

  Inductive expr :=
  | Var (x : var)
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  | LetIn (e1 : expr) (e2 : {bind expr}) 
  (* Base Types *)
  | Unit
  | Int (n : Z)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)
  (* If then else *)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* OSum *)
  | New (t : type) 
  | Case (l : loc)
  | Inj (sigma : expr )(e : expr)
  | CaseOf (d : expr) (i : expr) (e1 : {bind expr}) (e2 : expr)
  (* Polymorphic Types *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Existential Types *)
  | Pack (e : expr)
  | UnpackIn (e1 : expr) (e2 : {bind expr}).

  Global Instance Ids_expr : Ids expr. derive. Defined.
  Global Instance Rename_expr : Rename expr. derive. Defined.
  Global Instance Subst_expr : Subst expr. derive. Defined.
  Global Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Definition binop_res_type (op : binop) : type :=
  match op with
  | Add => TInt | Sub => TInt | Mult => TInt
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TInt
  | EqTBool : EqType TBool.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
  (* Notation for bool and nat *)
  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#n n" := (Int n) (at level 20).

(* note that gamma here is really a type environment *)
Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ

  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Int_typed n : Γ ⊢ₜ #n n : TInt
  | Bool_typed b : Γ ⊢ₜ #♭ b : TBool
  | Int_BinOp_typed op e1 e2 :
     Γ ⊢ₜ e1 : TInt →
     Γ ⊢ₜ e2 : TInt →
     Γ ⊢ₜ BinOp op e1 e2 : binop_res_type op
  | Eq_typed e1 e2 τ :
     EqType τ →
     Γ ⊢ₜ e1 : τ →
     Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ BinOp Eq e1 e2 : TBool
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 →
     Γ ⊢ₜ e2 : τ2 →
     Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  (* OSum *)
  | Inj_typed e1 e2 t1  : 
    Γ ⊢ₜ e1 : TCase t1 → 
    Γ ⊢ₜ e2 : t1 → 
    Γ ⊢ₜ Inj e1 e2 : TOSum 
  | CaseOf_typed e1 e2 e3 e4 t1 t2 :
    Γ ⊢ₜ e1 : TOSum -> 
    Γ ⊢ₜ e2 : TCase t1 ->
    t1 :: Γ ⊢ₜ e3 : t2 -> 
    Γ ⊢ₜ e4 : t2 ->
    Γ ⊢ₜ CaseOf e1 e2 e3 e4 : t2

  | New_typed t :  Γ ⊢ₜ (New t) : TCase t

  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Lam_typed e τ1 τ2 :
      τ1 :: Γ ⊢ₜ e : τ2 → 
      Γ ⊢ₜ Lam e : TArrow τ1 τ2

  | LetIn_typed e1 e2 τ1 τ2 :
    Γ ⊢ₜ e1 : τ1 → τ1 :: Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ LetIn e1 e2 : τ2

  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2

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

(*
Example bad : expr := 
  New 
    (TArrow TOSum TOSum)
    (Inj 
      (Var 0)
      (Lam (Var 0))).

Fail Inductive OSum' : Type :=
  | arr : (OSum' -> OSum') -> OSum'.
(* OSum := ... + (OSum -> OSum) + ...
would fail positivity check
*)
Example bad' : [] ⊢ₜ bad : TOSum.
Proof.
  eapply New_typed.
  eapply Inj_typed.
  - eapply Var_typed. reflexivity.
  - eapply Lam_typed. eapply Var_typed. reflexivity.
Qed.  

*)
(* example broken free theorem 
but this is not interpreting forall as fresh..
*)
Example idTy : type := TForall (TArrow(TVar 0) (TVar 0)).
Example notId : expr := 
  TLam (
    Lam (
      LetIn (New (TVar 0)) (
        (CaseOf (Inj (Var 0) (Var 1)) (Var 0) 
          (Var 2)
          (Var 1)
           )))).
Example broken : [] ⊢ₜ notId : idTy.
Proof.
  eapply TLam_typed.
  simpl.
  eapply Lam_typed.
  eapply LetIn_typed.
  -
  eapply New_typed.
  -
  eapply CaseOf_typed.
  +eapply Inj_typed.
    * eapply Var_typed. simpl. reflexivity.
    * eapply Var_typed ; reflexivity.
  + eapply Var_typed ; reflexivity.
  + eapply Var_typed. reflexivity.
  + eapply Var_typed. reflexivity.
Qed.


  Global Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof. solve_decision. Defined.

  Inductive val :=
  | LamV (e : {bind expr})
  | TLamV (e : {bind 1 of expr})
  | PackV (v : val)
  | UnitV
  | IntV (n : Z)
  | BoolV (b : bool)
  | PairV (v1 v2 : val)
  | InjV (v1 : val) (v2 : val)
  | CaseV (l : loc).

  (* Notation for bool and int *)
  Notation "'#♭v' b" := (BoolV b) (at level 20).
  Notation "'#nv' n" := (IntV n) (at level 20).

  Global Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof. solve_decision. Defined.

  Definition int_binop_eval (op : binop) : Z → Z → val :=
    match op with
    | Add => λ a b, #nv(a + b)
    | Sub => λ a b, #nv(a - b)
    | Mult => λ a b, #nv(a * b)
    | Eq => λ a b, #♭v (bool_decide (a = b))
    | Le => λ a b, #♭v (bool_decide (a ≤ b)%Z)
    | Lt => λ a b, #♭v (bool_decide (a < b)%Z)
    end.

  Definition binop_eval (op : binop) : val → val → option val :=
    match op with
    | Eq => λ a b, Some (#♭v (bool_decide (a = b)))
    | _ => λ a b,
        match a, b with
        | IntV an, IntV bn => Some (int_binop_eval op an bn)
        | _, _ => None
        end
    end.

  Global Instance val_inh : Inhabited val := populate UnitV.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | PackV v => Pack (of_val v)
    | UnitV => Unit
    | IntV v => Int v
    | BoolV v => Bool v
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjV v1 v2 => Inj (of_val v1) (of_val v2)
    | CaseV l => Case l
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Pack e => PackV <$> to_val e
    | Unit => Some UnitV
    | Int n => Some (IntV n)
    | Bool b => Some (BoolV b)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | Inj e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (InjV v1 v2)
    | Case l => Some (CaseV l)
    | _ => None
    end.



  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr) 
  | TAppCtx
  | PackCtx
  | UnpackInCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx (e2 : expr)
  | InjRCtx (v1 : val)
  | CaseOfCtxOSUM (e2 : expr) (e3 : {bind expr}) (e4 : expr)
  | CaseOfCtxInj (v1 : val) (e3 : {bind expr}) (e4 : expr)
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr}).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | LetInCtx e2 => LetIn e e2
    | TAppCtx => TApp e
    | PackCtx => Pack e
    | UnpackInCtx e2 => UnpackIn e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx e2 => Inj e e2
    | InjRCtx v1 => Inj (of_val v1) e
    | CaseOfCtxOSUM e2 e3 e4 => CaseOf e e2 e3 e4 
    | CaseOfCtxInj v1 e3 e4 => CaseOf (of_val v1) e e3 e4
    | IfCtx e1 e2 => If e e1 e2
    end.

  Definition state : Type := list loc.

  Inductive base_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* Lam-β *)
  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      base_step (App (Lam e1) e2) σ [] e1.[e2/] σ []

  | LetInBetaS e1 e2 v2 σ :
    to_val e1 = Some v2 →
    base_step (LetIn e1 e2) σ [] e2.[e1/] σ []

  (* Polymorphic Types *)
  (* no type substitution ..? just returns the body of the lambda?*)
  | TBeta e σ :
      base_step (TApp (TLam e)) σ [] e σ []
  (* Existential Types *)
  | UnpackS e1 v e2 σ :
      to_val e1 = Some v →
      base_step (UnpackIn (Pack e1) e2) σ [] e2.[e1/] σ []
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      base_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      base_step (Snd (Pair e1 e2)) σ [] e2 σ []

  (* bin op *)
  | BinOpS op a av b bv rv σ :
      to_val a = Some av →
      to_val b = Some bv →
      binop_eval op av bv = Some rv →
      base_step (BinOp op a b) σ [] (of_val rv) σ []

  (* If then else *)
  | IfFalse e1 e2 σ :
      base_step (If (#♭ false) e1 e2) σ [] e2 σ []
  | IfTrue e1 e2 σ :
      base_step (If (#♭ true) e1 e2) σ [] e1 σ []
  (* OSum *)
  | CaseOfTrue e1 e3 e4 v1 σ l l' :
    to_val e1 = Some v1 -> 
    l = l' -> (* use eq decide ? *)
    base_step 
        (CaseOf (Inj (Case l) e1) (Case l') e3 e4) σ [] 
        e3.[e1/] σ []

  | CaseOfFalse e1 e3 e4 v1 σ l l' :
    to_val e1 = Some v1 -> 
    l <> l' -> (* use eq decide ? *)
    base_step 
        (CaseOf (Inj (Case l) e1) (Case l') e3 e4) σ [] 
        e4 σ []

  | NewS t s :    
    base_step (New t) s [] (Case (fresh s)) (fresh s :: s) [].


  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.


  Global Instance of_val_inj : stdpp.base.Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (stdpp.base.inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Global Instance fill_item_inj Ki : stdpp.base.Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 κs e2 σ2 ef :
    base_step e1 σ1 κs e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma base_ctx_step_val Ki e σ1 κs e2 σ2 ef :
    base_step (fill_item Ki e) σ1 κs e2 σ2 ef → is_Some (to_val e).
  Proof.
    destruct Ki; try inversion_clear 1; try simplify_option_eq;  eauto.  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  Lemma val_base_stuck e1 σ1 κs e2 σ2 efs : base_step e1 σ1 κs e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.


  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item base_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck,
           fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.
End OSum.

Canonical Structure OSum_ectxi_lang :=
  EctxiLanguage OSum.lang_mixin.
Canonical Structure OSum_ectx_lang :=
  EctxLanguageOfEctxi OSum_ectxi_lang.
Canonical Structure OSum_lang :=
  LanguageOfEctx OSum_ectx_lang.

Export OSum.

Global Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Global Hint Extern 5 (IntoVal _ _) =>
  eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Global Hint Extern 5 (AsVal _) =>
  eexists; eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.
