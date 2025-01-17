From MyProject.src.SystemF Require Export SysF typing rules.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import upred iprop.
From iris.prelude Require Import options.
From iris.program_logic Require Import adequacy.

From iris.base_logic Require Import invariants.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
Module logrel.

Context `{irisGS SysF_lang Σ}.
Import SysF.

(*Local Notation "⊢ P" := (⊢@{iPropI Σ} P).
Local Notation "Q ⊢ P" := (Q ⊢@{iPropI Σ} P).
*)
Example arith : expr := BinOp Add (#n 3) (#n 7).

Example lem : iProp Σ := WP (#n 2) {{ v, True%I }}.

(* define a binary logical relation for SysF *)

Definition rel := (val * val) -> iPropI Σ.
Implicit Types rho : list rel.
Implicit Types interp : list rel -> rel.


(*

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
  *)
  
  (* why this definition?
  See section 8.3 of A Logical Approach to Type Soundess
 Definition interp_expr (τi : listO D -n> D) (Δ : listO D)
      (ee : expr * expr) : iProp Σ := (∀ j K,
    j ⤇ fill K (ee.2) -∗
    WP ee.1 {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ τi Δ (v, v') }})%I.
*)

(* see page 55 of A Logical Approach to Type Soundess *)

(* we don't need the thead specification thing
but this is pretty wrong...*)

 Definition interp_expr (interp : list rel -> rel) (rho : list rel) (ee : expr * expr) : iProp Σ := 
    (WP ee.1 {{ v1, 
        WP ee.2 {{ v2,  
        interp rho (v1, v2) }}}})%I.
   (* (WP ee.1 {{ v, ∃ v',  interp rho (v, v') }}
    ∧ WP ee.2 {{ v, ∃ v',  interp rho (v, v') }})%I.
*)

Program Definition interp_unit : list rel -> rel :=
fun rho => fun vv => 
    (⌜vv.1 = UnitV⌝ ∧ ⌜vv.2 = UnitV⌝)%I.

Program Definition interp_int : list rel -> rel :=
fun rho => fun vv => 
    (∃ n : Z, 
        ⌜vv.1 = #nv n⌝ ∧ 
        ⌜vv.2 = #nv n⌝)%I.

Program Definition interp_bool : list rel -> rel :=
fun rho => fun vv => 
    (∃ b : bool, 
        ⌜vv.1 = BoolV b⌝ ∧ 
        ⌜vv.2 = BoolV b⌝)%I.

Program Definition interp_prod (interp1 interp2 : list rel -> rel): list rel -> rel :=
fun rho => fun vv => 
    (∃ p1 p2, 
        ⌜vv = (PairV (p1.1) (p2.1), PairV (p1.2) (p2.2))⌝ ∧ 
        interp1 rho p1 ∧ 
        interp2 rho p2)%I.

Program Definition interp_sum (interp1 interp2 : list rel -> rel): list rel -> rel :=
fun rho => fun vv => 
    ((∃ p, ⌜vv = (InjLV (p.1), InjLV (p.2))⌝ ∧ interp1 rho p) ∨
    (∃ p, ⌜vv = (InjRV (p.1), InjRV (p.2))⌝ ∧ interp2 rho p))%I.

Program Definition interp_arrow (interp1 interp2 : list rel -> rel): list rel -> rel :=
fun rho => fun vv => 
    (∀ p, interp1 rho p -∗ 
        interp_expr 
            interp2
            rho 
            (
                App (of_val vv.1) (of_val p.1),
                App (of_val vv.2) (of_val p.2)
            ) )%I.

Program Definition interp_var (x : var) : list rel -> rel :=
fun rho => default ((λ _, True)%I) (rho !! x).

Program Definition interp_forall (interp : list rel -> rel): list rel -> rel :=
fun rho => fun vv => 
    (∀ (r : rel), 
        interp_expr 
            interp
            (r :: rho)
            (
                (TApp (of_val vv.1)),
                (TApp (of_val vv.2))
            ))%I.

Program Definition interp_exist (interp : list rel -> rel): list rel -> rel :=
fun rho => fun vv => 
    (∃ (r : rel) p, 
        ⌜vv = (PackV p.1, PackV p.2)⌝ ∗
        interp (r :: rho) p)%I.

Import typing.
 Fixpoint interp (t : type) : list rel -> rel :=
    match t return _ with
    | TUnit => interp_unit
    | TInt => interp_int
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => interp_var x
    | TForall τ' => interp_forall (interp τ')
    | TExist τ' => interp_exist (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : list rel) (vvs : list (val * val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).


Lemma tac_wp_pure `{!invGS Σ} Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "Hwp !> _" => //.
Qed.

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

Lemma tac_wp_expr_eval `{!invGS_gen hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

(*
(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, twp _ ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) _) =>
      eapply tac_twp_value
  end.
*)

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurrences of subst/fill *)
 (* try wp_value_head;  (* in case we have reached a value, get rid of the WP *)*)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)


Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    (fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_tlam" := wp_pure (TApp _  _).
Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (BoolV true) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (BoolV false) _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_lam" := wp_pure (App _ _).
Tactic Notation "wp_let" := wp_pure (LetIn _ _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Seq _ _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).



(* This defines the relational interpretation of types*)

(* play with this definition *)

Eval simpl in interp TUnit [] (UnitV,UnitV).

Definition r1 : rel := fun p => True%I.

(* the relation is not used here, no type variable *)
Example exprf : ⊢ interp TUnit [r1] (UnitV,UnitV).
Proof.
    simpl.
    unfold interp_unit.
    iPureIntro.
    eauto.
Qed.

Definition eqrel : rel := fun p => (⌜p.1 = p.2⌝)%I.

Definition idtype : type := 
    TForall (TArrow (TVar 0) (TVar 0)).


Definition e1 : val := TLamV (Lam (Var 0)).
Context (e2 : val).
Eval simpl in (interp idtype [] (e1 , e2)).

Definition p1 : iProp Σ := ∀ (e : expr), True.

(*
Example exprf1 e2 : ⊢ interp idtype [] (e1 , e2).
Proof.
    simpl.
    unfold interp_forall.
    simpl.
    
    iIntros.
    unfold interp_expr.
    wp_tlam.
    simpl.
    iApply wp_value.
    - compute. admit.
    - iApply wp_value.
    * admit.
    * unfold interp_arrow.
    intros.
Admitted.*)

Definition t1_type : type := 
  TForall 
    (TArrow 
      (TArrow 
        (TProd 
            (TVar 0)
            (TVar 0))
        (TVar 0))
      (TArrow 
        (TProd 
            (TVar 0)
            (TVar 0))
        (TVar 0))).

Example ex : 
    (interp t1_type []) = 
    interp_forall
        (interp_arrow 
            (interp_arrow 
                (interp_prod 
                    (interp_var 0) 
                    (interp_var 0)) 
                (interp_var 0))
            (interp_arrow 
                (interp_prod 
                    (interp_var 0) 
                    (interp_var 0)) 
                (interp_var 0))) [].
reflexivity.
Defined.

Eval simpl in interp t1_type [].



Definition bin_log_related (gamma : list type)(e e' : expr)(t : type) : iProp Σ :=
    (□ ∀ rho gammas, 
        ⟦ gamma ⟧* rho gammas -∗
        ⟦ t ⟧ₑ rho (e.[env_subst (gammas.*1)], e'.[env_subst (gammas.*2)]))%I.


Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Lemma interp_expr_val vv rho t : ⟦ t ⟧ rho vv -∗ ⟦ t ⟧ₑ rho (of_val vv.1, of_val vv.2).
Proof.
    destruct vv. 
    iIntros.
    iApply wp_value. 
    simpl.
    iApply wp_value.
    eauto.
Qed.

Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x ≤log≤ Var x : τ.
Admitted.

Lemma bin_log_related_unit Γ : ⊢ Γ ⊨ Unit ≤log≤ Unit : TUnit.
Proof.
    unfold bin_log_related.
    iModIntro.
    iIntros.
    simpl.
    unfold interp_expr.
    simpl.
    iApply wp_value.
    iApply wp_value.
    unfold interp_unit.
    simpl.
    eauto.
Qed.


Lemma bin_log_related_int Γ n : ⊢ Γ ⊨ #n n ≤log≤ #n n : TInt.
Admitted.

Lemma bin_log_related_bool Γ b : ⊢ Γ ⊨ #♭ b ≤log≤ #♭ b : TBool.
Admitted.




(*
Lemma test (p : type -> iProp Σ)  : ⊢ □ ∀ (p : type -> iProp Σ),  □ ∀ (t : type), p t%I.
Proof.
    pose TBool.
    iModIntro.
    iIntros.
    iModIntro.
    iIntros.
    iApply t.
*)

Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
Proof.
    iIntros "H1 H2".
    (*
    "H1" : Γ ⊨ e1 ≤log≤ e1' : τ1
    "H2" : Γ ⊨ e2 ≤log≤ e2' : τ2
    *)
    iDestruct "H1" as "#H1".
   (* iDestruct "H1" as "%H1". *)
    iDestruct "H2" as "#H2".
    unfold bin_log_related.
    iModIntro.
    iIntros (rho gammas) "ctx".

   (* iIntros "#rho #gammas". *)
    iIntros "%rho %gammas ctx".
    iSpecialize ("H1" with "rho").
    iDestruct ("H1" with "[rho //]") as "foo".



    iPoseProof ("⟦ Γ ⟧* rho0 gammas0 -∗
⟦ τ1 ⟧ₑ rho0 (e1.[env_subst gammas0.*1], e1'.[env_subst gammas0.*2])"). 


    simpl.
    unfold interp_env.
    iSpecialize "H1 rho" as #.
    iApply ("H1" $! rho).
    iModIntro.
    iIntros.
    
    simpl.
    iIntros "H1 H2".
    unfold bin_log_related.
    iMod "H1".
    iModIntro.
    unfold bin_log_related.
    iModIntro.
    iIntros.
    simpl.
    unfold interp_prod. 
    unfold interp_expr.
    iApply wp_value.
    - simpl. unfold IntoVal. admit.
    - simpl.
    iApply rho in 


Admitted.

Lemma bin_log_related_fst Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
Admitted.

Lemma bin_log_related_snd Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
Admitted.

Lemma bin_log_related_injl Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : τ1 -∗ Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
Admitted.

Lemma bin_log_related_injr Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : τ2 -∗ Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
Admitted.

Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3 -∗
    τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3 -∗
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
Admitted.


Lemma bin_log_related_if Γ e0 e1 e2 e0' e1' e2' τ :
    Γ ⊨ e0 ≤log≤ e0' : TBool -∗
    Γ ⊨ e1 ≤log≤ e1' : τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
Admitted.

Lemma bin_log_related_int_binop Γ op e1 e2 e1' e2' :
    Γ ⊨ e1 ≤log≤ e1' : TInt -∗
    Γ ⊨ e2 ≤log≤ e2' : TInt -∗
    Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
Admitted.

Lemma bin_log_related_Eq_binop Γ e1 e2 e1' e2' τ :
    EqType τ →
    Γ ⊨ e1 ≤log≤ e1' : τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ BinOp Eq e1 e2 ≤log≤ BinOp Eq e1' e2' : TBool.
Admitted.

Lemma bin_log_related_lam Γ e e' τ1 τ2 :
    τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
Admitted.

Lemma bin_log_related_letin Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    τ1 :: Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ LetIn e1 e2 ≤log≤ LetIn e1' e2': τ2.
Admitted.

Lemma bin_log_related_seq Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Seq e1 e2 ≤log≤ Seq e1' e2': τ2.
Admitted.

Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ1 -∗
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
Admitted.

Lemma bin_log_related_tlam Γ e e' τ :
    (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ -∗
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
Admitted.

Lemma bin_log_related_tapp Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : TForall τ -∗ Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
Admitted.

Lemma bin_log_related_pack Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : τ.[τ'/] -∗ Γ ⊨ Pack e ≤log≤ Pack e' : TExist τ.
Admitted.

Lemma bin_log_related_unpack Γ e1 e1' e2 e2' τ τ' :
    Γ ⊨ e1 ≤log≤ e1' : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 ≤log≤ e2' : τ'.[ren (+1)] -∗
    Γ ⊨ UnpackIn e1 e2 ≤log≤ UnpackIn e1' e2' : τ'.
Admitted.

Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e ≤log≤ e : τ.
Proof.
    induction 1.
    - iApply bin_log_related_var; done.
    - iApply bin_log_related_unit.
    - iApply bin_log_related_int.
    - iApply bin_log_related_bool.
    - iApply bin_log_related_int_binop; done.
    - iApply bin_log_related_Eq_binop; done.
    - iApply bin_log_related_pair; done.
    - iApply bin_log_related_fst; done.
    - iApply bin_log_related_snd; done.
    - iApply bin_log_related_injl; done.
    - iApply bin_log_related_injr; done.
    - iApply bin_log_related_case; done.
    - iApply bin_log_related_if; done.
    - iApply bin_log_related_lam; done.
    - iApply bin_log_related_letin; done.
    - iApply bin_log_related_seq; done.
    - iApply bin_log_related_app; done.
    - iApply bin_log_related_tlam; done.
    - iApply bin_log_related_tapp; done.
    - iApply bin_log_related_pack; done.
    - iApply bin_log_related_unpack; done.
Qed.

(* using the result *)
Definition gamma : list type := [].
Definition e : expr := 
    TLam (Lam (Var 0)).
Definition t : type := 
    TForall (TArrow (TVar 0) (TVar 0)).

Definition M : gamma ⊢ₜ e : t.
eapply TLam_typed.
eapply Lam_typed.
eapply Var_typed.
reflexivity.
Defined.

(* 
Definition bin_log_related (gamma : list type)(e e' : expr)(t : type) : iProp Σ :=
    (□ ∀ rho gammas, 
        ⟦ gamma ⟧* rho gammas -∗
        ⟦ t ⟧ₑ rho (e.[env_subst (gammas.*1)], e'.[env_subst (gammas.*2)]))%I.

*)
Eval simpl in binary_fundamental gamma e t M.

Check binary_fundamental gamma e t M.
(* no .. the binary fundamental blah blah just checks that interp is correct*)
Example hmm  e1 e2 : ⊢ interp idtype [eqrel] (e1 , e2).
Proof.
    pose (binary_fundamental gamma e t M).
    pose (rho := [eqrel]).
    pose (gammas := ([] : list (val * val))).
    unfold bin_log_related in b.
    assert (
        (⟦ t ⟧ₑ rho (e.[env_subst gammas.*1], e.[env_subst gammas.*2]))%I
    ).
    assert (
        ∀ rho (gammas : list (val * val)), ⟦ gamma ⟧* rho gammas -∗
⟦ t ⟧ₑ rho (e.[env_subst gammas.*1], e.[env_subst gammas.*2])
    ).
    - eauto.
    - apply l in H.
    iModIntro in b.
    iApply b in l.
    apply b in l.

End logrel.