From MyProject.src.SystemF Require Export SysF.
From iris.prelude Require Import options.


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

Definition binop_res_type (op : binop) : type :=
  match op with
  | Add => TInt | Sub => TInt | Mult => TInt
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

(* what is this ?*)
Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TInt
  | EqTBool : EqType TBool.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

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
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → 
     τ1 :: Γ ⊢ₜ e1 : τ3 → 
     τ2 :: Γ ⊢ₜ e2 : τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Lam_typed e τ1 τ2 :
      τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | LetIn_typed e1 e2 τ1 τ2 :
      Γ ⊢ₜ e1 : τ1 → τ1 :: Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ LetIn e1 e2 : τ2
  | Seq_typed e1 e2 τ1 τ2 :
      Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Seq e1 e2 : τ2
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

(* try some examples..
Lemma foo : [] ⊢ₜ BinOp Add (Int 1) (Int 2) : TInt.
Proof.
  eapply Int_BinOp_typed ; eapply Int_typed.
Qed.

(* (\x. x 1) (\y. y + y)*)
Definition p1 : expr := App (Lam (App (Var 0)(Int 1))) (Lam (BinOp Add (Var 0)(Var 0))).

Lemma foo1 : [] ⊢ₜ p1 : TInt.
Proof.
  unfold p1.
  apply App_typed with (τ1 := TArrow TInt TInt).
  - eapply Lam_typed. eapply App_typed.
    * eapply Var_typed. reflexivity.
    * eapply Int_typed.
  - apply Lam_typed.  apply Int_BinOp_typed ; apply Var_typed ; reflexivity.
  Qed.

(* "higher order" binop *)
(* t1 := (/\ X. \(f : X x X -> X).(\(p : X x X). f p) *)
Definition t1_type : type := 
  TForall 
    (TArrow 
      (TArrow 
        (TProd (TVar 0)(TVar 0))
        (TVar 0))
      (TArrow 
        (TProd (TVar 0)(TVar 0))
        (TVar 0))).

Definition t1_type' : type := 
    (TArrow 
      (TArrow 
        (TProd (TVar 0)(TVar 0))
        (TVar 0))
      (TArrow 
        (TProd (TVar 0)(TVar 0))
        (TVar 0))).
Definition t1 : expr := TLam (Lam (Lam (App (Var 1) (Var 0)))).
Lemma t1_typed : [] ⊢ₜ t1 : TForall t1_type'.
Proof.
  unfold t1.
  unfold t1_type.
  apply TLam_typed.
  apply Lam_typed.
  apply Lam_typed.
  eapply App_typed.
  - apply Var_typed. reflexivity.
  - apply Var_typed. reflexivity.
Qed.

(* tAdd := \(p : Int x Int). (fst x) + (snd x)  *)
Definition tAdd : expr := Lam(BinOp Add (Fst (Var 0)) (Snd (Var 0))).
Definition tAdd_type : type := 
  TArrow 
    (TProd (TInt)(TInt))
    (TInt).

Lemma tAdd_typed : [] ⊢ₜ tAdd : tAdd_type.
Proof.
  unfold tAdd. unfold tAdd_type.
  apply Lam_typed.
  apply Int_BinOp_typed.
  - eapply Fst_typed. apply Var_typed. reflexivity.
  - eapply Snd_typed. apply Var_typed. reflexivity.
Qed. 
(* tprog := t1[TInt](tAdd)(1 , 2) : Int*)
Definition tprog : expr := (App (App (TApp t1) tAdd) (Pair (Int 1)(Int 2))).

(* example performing type substitution *)
Eval simpl in t1_type.[TInt/].
Eval compute in t1_type.[TInt/].

Check subst.
Eval compute in subst (fun _ => TInt) t1_type.

(* huh *)
Eval compute in (TVar 0).[TInt/].
Eval compute in (TVar 1).[TInt/].
Eval compute in (TForall (TVar 0)).[TInt/].
Eval compute in (TForall (TVar 1)).[TInt/].



Eval compute in t1_type'.[TInt/].

(*
Lemma sub : [] ⊢ₜ TApp t1 : t1_type'.[TInt/].
Proof.
    apply TApp_typed with (e := t1)(τ := t1_type') (τ' := TInt).
    unfold t1.
    *)
Lemma tprog_typed : [] ⊢ₜ tprog : TInt.
Proof.
  unfold tprog.
  eapply App_typed.
  - eapply App_typed.
  * apply TApp_typed with (e := t1)(τ := t1_type') (τ' := TInt).
    apply t1_typed.
  * apply tAdd_typed.
  - compute. apply Pair_typed ; apply Int_typed.
  Qed. 


Definition p1 : expr :=
  TApp (Int 1).
Lemma foo2 : [TVar 1] ⊢ₜ p1 : TInt.
Proof.
  unfold p1.
  eapply TApp_typed.
*)
(* what?*)
Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end.

Eval compute in env_subst (IntV 8 :: BoolV true ::[]) .

Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x as [|x IH] => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IH.
Qed.
(*
Lemma typed_n_closed Γ τ e : Γ ⊢ₜ e : τ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  - rename select (_ !! _ = Some _) into H.
    apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia.
  - f_equal. eauto.
  - f_equal. rewrite ->length_fmap in *. done.
  - rewrite ->length_fmap in *; by f_equal.
Qed.



(** Weakening *)
Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ₜ e : τ →
  Γ' ++ ξ ++ Γ ⊢ₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ eqn:HeqΞ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl; eauto using typed.
  - rename select (_ !! _ = Some _) into Hlookup.
    rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in Hlookup.
    + asimpl. constructor. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in Hlookup; auto with lia.
      rename select var into x.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto.
    all: match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - econstructor; eauto.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => rename H into IH end.
    specialize (IH
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    rewrite ?length_map in IH.
    repeat rewrite fmap_app. apply IH.
    by repeat rewrite fmap_app.
  - econstructor; eauto.
    match goal with H : context[_ → _ ⊢ₜ _ : _.[ren (+1)]] |- _ => rename H into IH end.
    match goal with H : context[_ → _ ⊢ₜ _ : TExist ?t] |- _ => rename t into τ end.
    specialize (IH
      (τ :: (subst (ren (+1)) <$> Γ1)) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    asimpl in IH. rewrite ?length_map in IH.
    repeat rewrite fmap_app. apply IH.
    by repeat rewrite fmap_app.
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e : τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.
*)

End typing.