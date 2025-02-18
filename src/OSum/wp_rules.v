
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants saved_prop .
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Require Import Autosubst.Autosubst.

From MyProject.src.OSum Require Export OSum.

Class logrelSig  Σ := Resources {
    invariants : invGS Σ;
    predicates :: savedPredG Σ val ;
    names :: inG Σ (gsetR loc) ;
    name_set : gname
}.

Definition state_interp `{logrelSig Σ} (s : gset loc) : iProp Σ :=
    own name_set s.

Global Instance OSum_irisGS `{logrelSig Σ} : irisGS OSum_lang Σ := {
    iris_invGS := invariants;
    num_laters_per_step _ := 0;
    state_interp s  _ _ _ := state_interp s;(* gen_heap_interp s; *)
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section lang_rules.
    Context `{logrelSig Σ}.

    (*  All of the following is adopted from 
        A Logical Approach to Type Soundndess 
        

        Where this stuff comes into play is using rules like
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
        inversion H0 ; subst.
        { repeat (try split ; try reflexivity). } 
        exfalso.
        pose proof (H12 eq_refl). done.
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
        inversion H0. 
        { repeat (try split ; try reflexivity). exfalso. pose proof (ll H12). done. } 
         repeat (try split ; try reflexivity).
    Qed.


    Check gset_disj_alloc_updateP'.
    Check own_update.

(*     Lemma test (g : gname)(s : gset loc): own g s ⊢ |={⊤}=> own g s.
    Proof.
        iIntros "H".
        assert (s ~~> s).
        - done.
        -
        Check own_update.
        Fail iMod (own_update $! H0).
        Abort. *)

(* https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.locations.html#Loc.fresh *)
(*   Definition fresh (ls : gset loc) : loc :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls |}.

  Lemma fresh_fresh ls i : 0 ≤ i → fresh ls +ₗ i ∉ ls.
  Proof.
    intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh ls) + i).
    { intros help Hf%help. simpl in ×. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)));
      set_solver by eauto with lia.
  Qed. *)

  (* vs 
    stdpp.base.fresh
   *)

   Lemma fancyToBasic (P : iProp Σ ) : ⊢ (|==> P -∗ |={⊤}=> P)%I.
   Proof.
    iIntros.
    iModIntro.
    iIntros "HP".
    iModIntro. 
    iApply "HP".
    Qed.

    Lemma sub (s s' : state)(upd : s ~~> s') : own name_set s ⊢ |={⊤}=> own name_set s'.
    Proof.
        iIntros "H". 
        iMod (own_update name_set s s' upd with "H") as "H'".
        iModIntro. done.
    Qed.
(* WP (Case l).[env_subst gamma] {{ v, ⟦ TCase τ ⟧ rho v }}
 *)
(*     Lemma wp_new e v t : 
        IntoVal e v ->
        ⊢ WP (New t e) {{ v', True }}.
(*         {{{ True }}} New t e {{{ v', RET v'; True ∗ True }}}.
 *)    Proof.
        intros ev.
(*         iIntros (phi) "_ HPhi".
 *)        destruct ev.
        (* break into the guts WP using using the language lifting *)
        iApply wp_lift_atomic_base_step_no_fork; auto.
        iIntros (s1 n k1 k2 n') "#HStinterp".
        (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.

        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* need to show that we can summon a fresh location *)
        exact (is_fresh s1).
        - (* now we need to handle the state update, 
            first bring variables into scope  *)
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep; subst ; simpl.
        (*  Show that we can extend state s1 with a fresh location *)
        assert (s1 ~~> (s1 ∪ {[l]})) as update by done.
        (* now how do we use that update to modify name_set 
            using own_update? 
          first, we only need the ownership under the update modality
            so use the frame rules to shove things around  
        *)
        iApply fupd_frame_l.
        iSplit. { done. }
        iApply fupd_frame_r.
        (* here we need to make a choice w.r.t. the spacial context
           We dont need HPhi to prove ownership, but we do need it to show
           that the post condition holds, so push it to that goal  *)
        iSplitL "HStinterp".
        (* now we can update the name_set *)
        {
            iMod (own_update name_set s1 _ update with "HStinterp");
            iModIntro ; done. 
        }
        rewrite H2. done.
    Qed.
 *)



End lang_rules.





