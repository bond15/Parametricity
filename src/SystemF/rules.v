From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export gen_heap.
From MyProject.src.SystemF Require Export SysF.
From iris.prelude Require Import options.


From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.



Module rules.
Global Instance SysF_irisG `{invGS Σ} : irisGS SysF_lang Σ := {
  num_laters_per_step _ := 0;
  state_interp σ  _ _ _ := True%I;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Import uPred.

Import SysF.

Section lang_rules.
  Context `{invGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val  → iProp Σ.
  Implicit Types σ : state .
  Implicit Types e : expr .
  Implicit Types v w : val .


  Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors base_step : core.
  Local Hint Resolve to_of_val : core.

  Local Ltac solve_exec_safe :=
    intros; subst; do 3 eexists; econstructor; simpl; eauto.

  Local Ltac solve_exec_puredet :=
    simpl; intros;
      repeat match goal with
          |- context [bool_decide ?A] =>
            destruct (decide A);
            [rewrite (bool_decide_eq_true_2 A); last done|
             rewrite (bool_decide_eq_false_2 A); last done]
        end; simplify_eq/=; auto.

  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
    PureExec True 1 (LetIn e1 e2) e2.[e1 /].
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_seq e1 e2 `{!AsVal e1} :
    PureExec True 1 (Seq e1 e2) e2.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_tlam e : PureExec True 1 (TApp (TLam e)) e.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_pack e1 `{!AsVal e1} e2:
    PureExec True 1 (UnpackIn (Pack e1) e2) e2.[e1/].
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance wp_if_true e1 e2 :
    PureExec True 1 (If (#♭ true) e1 e2) e1.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.

  Global Instance wp_if_false e1 e2 :
    PureExec True 1 (If (#♭ false) e1 e2) e2.
  Proof. solve_pure_exec. inversion H0. eauto. Qed.


  Global Instance wp_int_binop op a b :
    PureExec True 1 (BinOp op (#n a) (#n b)) (of_val (int_binop_eval op a b)).
  Proof. destruct op; solve_pure_exec ;inversion H0 ; repeat (split ; eauto);
        eapply of_to_val; rewrite <- H11; simplify_option_eq ; try (reflexivity) 
        ; pose (False);
        contradiction.
     Qed.


  Global Instance wp_Eq_binop `{!AsVal e1} `{!AsVal e2} :
    PureExec True 1 (BinOp Eq e1 e2) (#♭ (bool_decide (e1 = e2))).
  Proof. solve_pure_exec ;inversion H0 ; repeat (split ; eauto).
    - eapply of_to_val; rewrite <- H11. simplify_option_eq.
        f_equal. f_equal. 
        symmetry. eapply bool_decide_eq_true_2. reflexivity.
    Admitted.

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


End lang_rules.
End rules.