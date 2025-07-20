From MyProject.src.OSum Require Export OSum.
Require Import Autosubst.Autosubst.

Module CtxEquiv.
Print type.
Print expr.

(* inductive definition of a hole in an expr.
 the derivative of a polynomial functor 
 representing the syntax/constructors
*)
Inductive ctx_item := 
    | ctx_appL (e : expr)
    | ctx_appR (e : expr)
    | ctx_lam 

    | ctx_letL (e : expr)
    | ctx_letR (e : expr)

    | ctx_binOpL (op : binop) (e : expr)
    | ctx_binOpR (op : binop) (e : expr)

    | ctx_prodL (e : expr)
    | ctx_prodR (e : expr)
    | ctx_fst 
    | ctx_snd
    
    | ctx_ifL (e e' : expr)
    | ctx_ifM (e e' : expr)
    | ctx_ifR (e e' : expr)

    | ctx_injSig (e : expr)
    | ctx_injVal (e : expr)

    | ctx_caseOsum (e e' e'' : expr)
    | ctx_caseSig (e e' e'' : expr)
    | ctx_caseTrue (e e' e'' : expr)
    | ctx_caseFalse (e e' e'' : expr)

    | ctx_Tlam 
    | ctx_Tapp

    | ctx_pack
    | ctx_unpackL (e : expr)
    | ctx_unpackR (e : expr).

(* well typed holes/context *)
Inductive typed_ctx_item : 
        (* which type of hole  *)
        ctx_item -> 
        (* type of the hole *)
        list type -> type -> 
        (* type of the whole *)
        list type -> type -> 
        Prop := 
    
    (* App _ e *)
    | tp_ctx_appL G t1 t2 e :
        typed G e t1 ->
        typed_ctx_item (ctx_appL e)
            G (TArrow t1 t2)
            G (t2)

    (* App f _ *)
    | tp_ctx_appR G t1 t2 f :
        typed G f (TArrow t1 t2) -> 
        typed_ctx_item (ctx_appR f) 
            G t1  
            G t2

    (* Lam _ *)
    | tp_ctx_lam G t t' : 
        typed_ctx_item ctx_lam 
            (t :: G) t'
            G (TArrow t t')
         
    (* let x = _ in M *) 
    | tp_ctx_letL G t1 t2 M : 
        typed (t1 :: G) M t2 ->
        typed_ctx_item (ctx_letL M) 
            G t1
            G t2

    (* let x = e in _ *)
    | tp_ctx_letR G t1 t2 e : 
        typed G e t1 -> 
        typed_ctx_item (ctx_letR e)
            (t1 :: G) t2 
            G t2

    (*  binops *)
    (* (_ , e) *)
    | tp_ctx_prodL G e t1 t2 : 
        typed G e t2 -> 
        typed_ctx_item (ctx_prodL e)
            G t1 
            G (TProd t1 t2)
    
    (* (e , _) *)
    | tp_ctx_prodR G e t1 t2 :
        typed G e t1 -> 
        typed_ctx_item (ctx_prodR e)
            G t2
            G (TProd t1 t2)

    (* fst _ *)
    | tp_ctx_fst G t1 t2 :
        typed_ctx_item (ctx_fst)
            G (TProd t1 t2)
            G t1
    
    (* snd _ *)
    | tp_ctx_snd G t1 t2 : 
        typed_ctx_item (ctx_snd)
            G (TProd t1 t2)
            G t2

    (* if _ then e else e' *)
    | ty_ctx_ifL G t e e' : 
        typed G e t -> 
        typed G e' t -> 
        typed_ctx_item (ctx_ifL e e')
            G TBool 
            G t
    
    (* if e then _ else e' *)
    | ty_ctx_ifM G t e e' : 
        typed G e TBool -> 
        typed G e' t ->
        typed_ctx_item (ctx_ifM e e')
            G t 
            G t 

    (* if e then e' else _ *)
    | ty_ctx_ifR G t e e' : 
        typed G e TBool -> 
        typed G e' t -> 
        typed_ctx_item (ctx_ifR e e')
            G t 
            G t 

    (* Inj _ e *)
    | ty_ctx_injSig G t e : 
        typed G e t -> 
        typed_ctx_item (ctx_injSig e)
            G (TCase t)
            G TOSum

    (* Inj s _ *)
    | ty_ctx_injVal G t s : 
        typed G s (TCase t) -> 
        typed_ctx_item (ctx_injVal s) 
            G t 
            G TOSum

    (* case _ of e {e' | e''} *)
    | ty_ctx_caseOsum G t t' e e' e'' :
        typed G e (TCase t) ->
        typed (t :: G) e' t' -> 
        typed G e'' t' -> 
        typed_ctx_item (ctx_caseOsum e e' e'')
            G TOSum
            G t'
    
    (* case e of _ {e' | e''} *)
    | ty_ctx_caseSig G t t' e e' e'' : 
        typed G e TOSum -> 
        typed (t :: G) e' t' -> 
        typed G e'' t' -> 
        typed_ctx_item (ctx_caseSig e e' e'' )
            G (TCase t)
            G t'

    (* case e of e' {_ | e''} *)
    | ty_ctx_caseTrue G t t' e e' e'' : 
        typed G e TOSum -> 
        typed G e' (TCase t) -> 
        typed G e'' t' -> 
        typed_ctx_item (ctx_caseTrue e e' e'')
            (t :: G) t' 
            G t' 

    (* case e of e' {e'' | _} *)
    | ty_ctx_caseFalse G t t' e e' e'' :
        typed G e TOSum -> 
        typed G e' (TCase t) -> 
        typed (t :: G) e'' t' ->
        typed_ctx_item (ctx_caseFalse e e' e'')
            G t' 
            G t'

    (* TLam _ *)
    | ty_ctx_Tlam G t: 
        typed_ctx_item ctx_Tlam 
            (subst (ren (+1)) <$> G) t
            G (TForall t)

    (* TApp _ *)
    | ty_ctx_Tapp G t t' : 
        typed_ctx_item ctx_Tapp
            G (TForall t) 
            G t.[t'/]

    
    (* pack _  *)
    | ty_ctx_pack G t t' : 
        typed_ctx_item ctx_pack
            G t.[t'/]
            G (TExist t)
    (* unpack x = _ in e *)
    | ty_ctx_unpackL G t t' e : 
        typed (t :: (subst (ren (+1)) <$> G)) e t'.[ren (+1)] ->
        typed_ctx_item (ctx_unpackL e)
            G (TExist t)
            G t'

    (* unpack x = e in _ *)
    | ty_ctx_unpackR G t t' e: 
        typed G e (TExist t) -> 
        typed_ctx_item (ctx_unpackR e)
            (t :: (subst (ren (+1)) <$> G)) t'.[ren (+1)]
            G t'.
    
(* plug - fill the hole *)
Definition plug_item (ctx : ctx_item) (h : expr) : expr := 
    match ctx with 
        | ctx_appL e => App h e 
        | ctx_appR e => App e h 
        | ctx_lam => Lam h 
        | ctx_letL e => LetIn h e 
        | ctx_letR e => LetIn e h 
        | ctx_binOpL op e => BinOp op h e 
        | ctx_binOpR op e => BinOp op e h 
        | ctx_prodL e => Pair h e 
        | ctx_prodR e => Pair e h 
        | ctx_fst => Fst h 
        | ctx_snd => Snd h 
        | ctx_ifL e e' => If h e e' 
        | ctx_ifM e e' => If e h e' 
        | ctx_ifR e e' => If e e' h 
        | ctx_injSig e => Inj h e 
        | ctx_injVal e => Inj e h 
        | ctx_caseOsum e e' e'' => CaseOf h e e' e'' 
        | ctx_caseSig e e' e'' => CaseOf e h e' e'' 
        | ctx_caseTrue e e' e'' => CaseOf e e' h e'' 
        | ctx_caseFalse e e' e'' => CaseOf e e' e'' h 
        | ctx_Tlam => TLam h 
        | ctx_Tapp => TApp h 
        | ctx_pack => Pack h 
        | ctx_unpackL e => UnpackIn h e 
        | ctx_unpackR e => UnpackIn e h 
    end.

(* build up a context from ctx_items *)

Definition ctx := list ctx_item.

Definition plug (K : ctx)(e : expr) : expr := foldr plug_item e K.

(* pluging in a value of the right type 
yields a well typed expression*)

Lemma typed_ctx_item_typed K G t t' e :
    typed G e t -> 
    typed_ctx_item K G t G t' -> 
    typed G (plug_item K e) t'.
Proof.
    (* all of the admits here just need weakening of contexts*)
    intros.
    induction H0; simpl; eauto using typed.
    - apply Lam_typed. admit.
    - eapply LetIn_typed. exact H0. admit.
    - eapply CaseOf_typed. exact H0. exact H1. 2:{ exact H2. } admit.
    - eapply TLam_typed. admit.
    - eapply UnpackIn_typed. exact H0. admit.
Admitted.

(* a ctx is well typed if each layer is well typed *)
Inductive typed_ctx: ctx → list type → type → list type → type → Prop :=
  | TPCTX_nil Γ τ :
     typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
     typed_ctx_item k Γ2 τ2 Γ3 τ3 →
     typed_ctx K Γ1 τ1 Γ2 τ2 →
     typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (plug K e) τ'.
Proof. 
    intros.
    induction H0.
    - simpl. exact H.
    - pose proof (IHtyped_ctx H).
    eapply typed_ctx_item_typed.
Admitted.

(* definition of contextual refinement *)
Definition reduces K e := exists v s, rtc erased_step ([plug K e],[])([of_val v],s).

Definition ctx_refines (G : list type)(e e' : expr)(t : type) := 
    (typed G e t) -> 
    (typed G e' t) -> 
    forall K, (
        typed_ctx K G t [] TUnit -> 
        reduces K e -> 
        reduces K e'
    ). 
(* Definition ctx_refines (G : list type)(e e' : expr)(t : type) := 
    (typed G e t) -> 
    (typed G e' t) -> 
    forall K s v, (
        typed_ctx K G t [] TUnit -> 
        rtc erased_step ([plug K e], []) ([of_val v], s) -> 
        reduces K e'
    ). *)


Notation "Γ ⊨ e '≤ctx≤' e' : τ" :=
  (ctx_refines Γ e e' τ) (at level 74, e, e', τ at next level).

  (*  examples *)
(* 
Print ectx_item.
Definition convert (K : ectx_item) : ctx_item := 
match K with 
| AppLCtx e => ctx_appL e
| AppRCtx e => ctx_appR (of_val e)
| LetInCtx e => ctx_letL e
| TAppCtx  => ctx_Tapp
| PackCtx => ctx_pack
| UnpackInCtx e => ctx_unpackL e
| PairLCtx e => ctx_p
end. *)

Example try : [] ⊨ (Bool true) ≤ctx≤ (If (Bool true) (Bool true) (Bool false)) : TBool.
Proof.
    unfold ctx_refines.
    intros.
    destruct H2.
    destruct H2.
    exists x. exists x0.
    econstructor.
    2:{ exact H2. }
    unfold erased_step.
    exists [].
    econstructor.
    3:{ econstructor. 3:{  apply IfTrue. }
    reflexivity.
    reflexivity.
    }
    -
    admit.
Abort.


End CtxEquiv.