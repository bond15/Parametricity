From Autosubst Require Export Autosubst.

From stdpp Require Export base decidable.
Module SysF.


  Inductive expr :=
  | Var (x : var)
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  (* Base Types *)
  | Unit
  | Bool (b : bool)
  (* If then else *)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
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


(*   Global Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof. solve_decision. Defined. *)

  Inductive val :=
  | LamV (e : {bind expr})
  | TLamV (e : {bind 1 of expr})
  | PackV (v : val)
  | UnitV
  | BoolV (b : bool)
  | PairV (v1 v2 : val).


(*   Global Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof. solve_decision. Defined. *)


  Global Instance val_inh : Inhabited val := populate UnitV.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | PackV v => Pack (of_val v)
    | UnitV => Unit
    | BoolV v => Bool v
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    end.

End SysF.
(*   Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Pack e => PackV <$> to_val e
    | Unit => Some UnitV
    | Bool b => Some (BoolV b)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | _ => None
    end. *)
(* 
  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | PackCtx
  | UnpackInCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr}).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | LetInCtx e2 => LetIn e e2
    | SeqCtx e2 => Seq e e2
    | TAppCtx => TApp e
    | PackCtx => Pack e
    | UnpackInCtx e2 => UnpackIn e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | IfCtx e1 e2 => If e e1 e2
    end.


  Definition state : Type := ().

(* Note that all of these rules effectivly ignore the 2nd, 3rd, 5th, and 6th arguements
So really base_step : expr -> expr -> Prop
this makes sense with pure SystemF
*)
  Inductive base_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* Lam-β *)
  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      base_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
  (* LetIn-β *)
  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      base_step (LetIn e1 e2) σ [] e2.[e1/] σ []
  (* Seq-β *)
  (* wait what.. just returns e2 ..?*)
  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      base_step (Seq e1 e2) σ [] e2 σ []
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      base_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      base_step (Snd (Pair e1 e2)) σ [] e2 σ []
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      base_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      base_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
    (* nat bin op *)
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
  (* Polymorphic Types *)
  (* no type substitution ..? just returns the body of the lambda?*)
  | TBeta e σ :
      base_step (TApp (TLam e)) σ [] e σ []
  (* Existential Types *)
  | UnpackS e1 v e2 σ :
      to_val e1 = Some v →
      base_step (UnpackIn (Pack e1) e2) σ [] e2.[e1/] σ [].

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 κs e2 σ2 ef :
    base_step e1 σ1 κs e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma base_ctx_step_val Ki e σ1 κs e2 σ2 ef :
    base_step (fill_item Ki e) σ1 κs e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

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
End SysF.

Canonical Structure SysF_ectxi_lang :=
  EctxiLanguage SysF.lang_mixin.
Canonical Structure SysF_ectx_lang :=
  EctxLanguageOfEctxi SysF_ectxi_lang.
Canonical Structure SysF_lang :=
  LanguageOfEctx SysF_ectx_lang.

Export SysF.

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
 *)