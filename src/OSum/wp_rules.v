
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants saved_prop .
From iris.algebra Require Import gset gmap big_op gset_bij.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import ghost_map gset_bij.


Require Import Autosubst.Autosubst.

From MyProject.src.OSum Require Export persistent_pred OSum.



Section lang_rules.
(*     Context `{logrelSig Σ}.
 *)
    (*  All of the following is adopted from 
        A Logical Approach to Type Soundndess 
        

        Where PureExec stuff comes into play is using rules like
            wp_pure_step_later    
            the obligations can be automatically dispatched 
                by adding the following hints to the database

        This helps avoid breaking into the lower level lemmas such as
            wp_lift_pure_det_base_step_no_fork 
    *)

    Ltac inv_base_step :=
        repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : _ = of_val ?v |- _ =>
            is_var v; destruct v; first[discriminate H|injection H as H]
        | H : base_step ?e _ _ _ _ _ |- _ =>
            try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
            and can thus better be avoided. *)
            inversion H; subst; clear H
        end.

(*     Local Hint Extern 0 (atomic _) => solve_atomic : core.*)
    Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.

    Local Hint Constructors base_step : core.

    Local Hint Resolve to_of_val : core.


    Local Ltac solve_exec_safe :=
        intros; subst; do 3 eexists; econstructor; simpl; eauto.

    Local Ltac solve_exec_puredet :=
        simpl; intros;
        by inv_base_step;
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
    Proof. solve_pure_exec. Qed.

    Global Instance pure_tlam e : PureExec True 1 (TApp (TLam e)) e.
    Proof. solve_pure_exec. Qed.

    Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
        PureExec True 1 (LetIn e1 e2) e2.[e1 /].
    Proof. solve_pure_exec. Qed.

    Global Instance pure_pack e1 `{!AsVal e1} e2:
        PureExec True 1 (UnpackIn (Pack e1) e2) e2.[e1/].
    Proof. solve_pure_exec. Qed.

    Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
        PureExec True 1 (Fst (Pair e1 e2)) e1.
    Proof. solve_pure_exec. Qed.

    Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
        PureExec True 1 (Snd (Pair e1 e2)) e2.
    Proof. solve_pure_exec. Qed.


    Global Instance wp_if_true e1 e2 :
        PureExec True 1 (If (#♭ true) e1 e2) e1.
    Proof. solve_pure_exec. Qed.

    Global Instance wp_if_false e1 e2 :
        PureExec True 1 (If (#♭ false) e1 e2) e2.
    Proof. solve_pure_exec. Qed.

    Global Instance wp_int_binop op a b :
        PureExec True 1 (BinOp op (#n a) (#n b)) (of_val (int_binop_eval op a b)).
    Proof. destruct op; solve_pure_exec. Qed.

    Global Instance wp_Eq_binop `{!AsVal e1} `{!AsVal e2} :
        PureExec True 1 (BinOp Eq e1 e2) (#♭ (bool_decide (e1 = e2))).
    Proof. solve_pure_exec. Qed.

    Global Instance wp_case_match  l `{!AsVal e2} (e3 e4 : expr)  : 
        PureExec True 1 (CaseOf (Inj (Case l) e2) (Case l) e3 e4) e3.[e2/].
    Proof. unfold PureExec. intros _.
        destruct AsVal0. subst.
        apply nsteps_once. apply pure_base_step_pure_step.
        constructor.
        {
            intros. repeat eexists. eapply CaseOfTrue. - apply to_of_val.
            - reflexivity.
        }
        intros.
        inversion H ; subst.
        { repeat (try split ; try reflexivity). } 
        exfalso.
        pose proof (H11 eq_refl). done.
    Qed.

    Global Instance wp_case_nomatch l l' `{!AsVal e2} (e3 e4 : expr)  : 
        l <> l' -> PureExec True 1 (CaseOf (Inj (Case l) e2) (Case l') e3 e4) e4.
    Proof. unfold PureExec. intros ll _.
        destruct AsVal0. subst.
        apply nsteps_once. apply pure_base_step_pure_step.
        constructor.
        {
            intros. repeat eexists. eapply CaseOfFalse. - apply to_of_val.
            - exact ll.
        }
        intros.
        inversion H. 
        { repeat (try split ; try reflexivity). exfalso. pose proof (ll H11). done. } 
         repeat (try split ; try reflexivity).
    Qed.

End lang_rules.
