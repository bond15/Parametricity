From stdpp Require Import base gmap coPset tactics proof_irrel.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import cofe_solver gset gmap_view excl.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre ectx_lifting.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.OSum Require Export OSum logrel.


Fixpoint env_subst (vs : list val) : var → expr :=
match vs with
| [] => ids
| v :: vs' => (of_val v) .: env_subst vs'
end.

Check interp_env.
Definition log_typed `{logrelSig Σ} (Γ : list type) (e : expr) (τ : type) : iProp Σ :=
    (□ ∀ rho (vs : list val), ⟦ Γ ⟧* rho vs -∗ ⟦ τ ⟧ₑ rho e.[env_subst vs])%I.

Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Module fund.
  
    Import OSum.

    Context`{logrelSig Σ}.

    Lemma interp_expr_bind K e Δ τ τ' :
        ⟦ τ ⟧ₑ Δ e -∗ (∀ v, ⟦ τ ⟧ Δ v -∗ ⟦ τ' ⟧ₑ Δ (fill K (of_val v))) -∗ ⟦ τ' ⟧ₑ Δ (fill K e).
    Proof.
        (* Recall interp_expr := (WP e {{ v, ⟦ τ ⟧ rho v }}) *)
        iIntros.
        Check wp_bind.
        (* 
            wp_bind :=  WP e {{ v, WP (K (of_val v)) {{ v, Φ v }} }} ⊢ WP (K e) {{ v, Φ v }}
            
            If goal is a weakest precondition 
                where the expression is some evaluation context applied to an expressions,

            Then you can factor that into nested weakest preconditions which 
                first, evaluate the expression e to a value v,
                second, return the weakest precondition of the evaluation context applied to the 
                    value v
        *)
        iApply wp_bind.
        (* 
            Use to adjust the postcondition 

            Lemma wp_wand s E e Φ Ψ :
                WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
        *)
        Check wp_wand.
        iApply (wp_wand with "[$]").
        done.
    Qed.


    Lemma env_subst_lookup vs x v :
    vs !! x = Some v → env_subst vs x = of_val v.
    Proof.
    revert vs; induction x as [|x IH] => vs.
    - by destruct vs; inversion 1.
    - destruct vs as [|w vs]; first by inversion 1.
        rewrite -lookup_tail /=.
        apply IH.
    Qed.

    Lemma sem_typed_var Γ x τ :
        Γ !! x = Some τ → ⊢ Γ ⊨ Var x : τ.
    Proof.
        iIntros (? Δ vs) "!# #HΓ"; simpl.
        iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
        erewrite env_subst_lookup; eauto.
        iApply wp_value; done.
    Qed.

    Lemma sem_typed_case Γ l x τ :
          Γ !! x = Some (TCase τ) → ⊢ Γ ⊨ Case l : TCase τ.
    Proof.
        iIntros (asm rho gamma) "!# #HG".
        (* case is a value *)
        iApply wp_value.
        Check interp_env_Some_l.
        iDestruct (interp_env_Some_l with "HG") as (v) "[% H]"; first done.

        iDestruct ("H") as "[%l' (H1 & H2)]".
        iExists l.
        iSplit. iPureIntro. reflexivity.
        (* The assumption for this lemma is not strong enough...
            would have to modify interp_env_Some_l
            
            Should we really have this rule anyway? It is for typing dynamic expressions.
         *)
       Abort.



    Lemma sem_typed_unit Γ : ⊢ Γ ⊨ Unit : TUnit.
    Proof.
        iIntros (rho gamma) "!# _" .
        unfold interp_expr.
        unfold interp.
        unfold interp_TUnit.
        simpl.
        iApply wp_value.
        done.
    Qed.

    Lemma sem_typed_int Γ (n : nat) : ⊢ Γ ⊨ #n n : TInt.
    Proof.
        iIntros (rho gamma) "!# _".
        iApply wp_value.
        iExists n.
        done.
    Qed.

    Lemma sem_typed_bool Γ b : ⊢ Γ ⊨ #♭ b : TBool.
    Proof.
        iIntros (rho gamma) "!# _".
        iApply wp_value.
        iExists b.
        done.
    Qed.

    Lemma sem_typed_pair Γ e1 e2 τ1 τ2 :
        Γ ⊨ e1 : τ1 -∗
        Γ ⊨ e2 : τ2 -∗
        Γ ⊨ Pair e1 e2 : TProd τ1 τ2.
    Proof.
        iIntros "#H1 #H2" (rho gamma) "!# #HG". simpl.
        Print PairLCtx.
        Print fill_item.
        Print fill.
        Eval simpl in fill [PairLCtx Unit] Unit. 
        Check interp_expr_bind [PairLCtx _].
        (* 
            ⟦ TProd τ1 τ2 ⟧ₑ rho (Pair e1.[env_subst gamma] e2.[env_subst gamma])

            Here we are interpreting a pair of two expressions e1,e2 according to interp_TProd
            
            To break this appart, interp_expr_bind to get the first expression e1 to a value.
        *)
        iApply (interp_expr_bind [PairLCtx _ ]).
        - iApply "H1". done.
        - iIntros (v1) "#Hv1". simpl.
        (* 
            ⟦ TProd τ1 τ2 ⟧ₑ rho (Pair (of_val v) e2.[env_subst gamma])

            Now, work on getting the second expression to a value
        *)
        iApply (interp_expr_bind [PairRCtx _ ]).
        + iApply "H2". done.
        + iIntros (v2) "#Hv2". simpl.
        Check interp_expr.
        (* 
            ⟦ TProd τ1 τ2 ⟧ₑ rho (Pair (of_val v1) (of_val v2))

            Recall interp_expr := (WP e {{ v, ⟦ τ ⟧ rho v }})

            so the goal is really
                WP Pair (of_val v1) (of_val v2) {{ v, ⟦ TProd τ1 τ2 ⟧ rho v }}

            and we can use wp_value to dispatch this.
        *)
        unfold interp_expr.
        iApply wp_value.
        (* 
            Now we just need to prove the value relation
            
            ⟦ TProd τ1 τ2 ⟧ rho (PairV v1 v2)

            Recall interp_TProd  := 
                λne rho, PersPred(fun v => (∃ v1 v2 , ⌜v = PairV v1 v2⌝  ∗ interp1 rho v1  ∗ interp2 rho v2))%I.  
        *)
        simpl.
        iExists v1. iExists v2.
        iSplit.
        {done. }
        iSplit.
        { iApply "Hv1". }
        iApply "Hv2".
    Qed.


    Lemma sem_typed_fst Γ e τ1 τ2 : Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Fst e : τ1.
    Proof.
        iIntros "#HP " (rho gamma) "!# #HG".
        iSpecialize ("HP" $! rho gamma with "HG").
        (* use interp_expr_ind to get to a value*)
        iApply (interp_expr_bind [FstCtx]).
        - iApply "HP".
        - iIntros (v) "#HV".
        (*
            Now we have some value, v, which is interpreted as a product type. 
            So we know it should be able to split into a pair of values
        *)
        iEval (simpl) in "HV".
        iDestruct "HV" as "[%v1 [%v2 (%vPair & interp_v1 & interp_v2)]]".
        subst.
        (* 
            now we can show that since v = (v1, v2), fst v = v1
        *)
        simpl.
        iApply wp_pure_step_later; try done.
        iModIntro. iIntros. iApply wp_value. iApply "interp_v1".
    Qed.


    Lemma sem_typed_snd Γ e τ1 τ2 : Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Snd e : τ2.
    Proof.
        iIntros "#HP " (rho gamma) "!# #HG".
        iSpecialize ("HP" $! rho gamma with "HG").
        (* use interp_expr_ind to get to a value*)
        iApply (interp_expr_bind [SndCtx]).
        - iApply "HP".
        - iIntros (v) "#HV".
        (*
            Now we have some value, v, which is interpreted as a product type. 
            So we know it should be able to split into a pair of values
        *)
        iEval (simpl) in "HV".
        iDestruct "HV" as "[%v1 [%v2 (%vPair & interp_v1 & interp_v2)]]".
        subst.
        (* 
            now we can show that since v = (v1, v2), fst v = v1
        *)
        simpl.
        iApply wp_pure_step_later; try done.
        iModIntro. iIntros. iApply wp_value. iApply "interp_v2".
    Qed.


    (* Do arrow and then try OSum related ones *)

    Lemma sem_typed_lam Γ e τ1 τ2 : τ1 :: Γ ⊨ e : τ2 -∗ Γ ⊨ Lam e : TArrow τ1 τ2.
    Proof.
        iIntros "#HP" (rho gamma) "!# #HG". 
        iSpecialize ("HP" $! rho). (* can't specialize further without a value *)
        (*  lam is already a value *)
        iApply wp_value. 
        (*
            recall interp_TArrow := 

                λne rho, PersPred(fun v => 
                    (□ ∀ v', interp1 rho v' → WP App (of_val v) (of_val v') {{ interp2 rho }}))%I. 
        *)
        simpl. iModIntro. iIntros (v') "#Hv'".
        (*  further specialize HP since we have a value *)
        iSpecialize ("HP" $! (v' :: gamma)).

        (*  Application is a pure step, as we've defined in wp_rules *)
        Check pure_lam.
        iApply wp_pure_step_later ; try done.
        iIntros "!> _". (* discard the later credit *)
        asimpl. (* autosubst tactic performing substitution *)
        (* Now we can use our initial assumption *) 
        iApply "HP".
        (* at this point, we need to use the assumptions about the contexts *)
        iApply interp_env_cons.
        iSplit ; done.
    Qed.


    Lemma sem_typed_app Γ e1 e2 τ1 τ2 : 
        Γ ⊨ e1 : TArrow τ1 τ2 -∗ 
        Γ ⊨ e2 : τ1 -∗ 
        Γ ⊨ App e1 e2 : τ2.
    Proof.
        iIntros "#H1 #H2" (rho gamma) "!# #HG".
        iSpecialize ("H1" $! rho gamma with "HG"). 
        iSpecialize ("H2" $! rho gamma with "HG"). 
        (* similar to product, we need to reduce the expressions to values
        so we can take a step of computation *)
        Check AppLCtx.
        iApply (interp_expr_bind [AppLCtx _]).
        { iApply "H1". }
        iIntros (v) "HV". simpl.
        iApply (interp_expr_bind [AppRCtx _]).
        { iApply "H2". }
        iIntros (v') "#HV'". simpl.
        (* all we have to do here is apply HV *)
        iApply "HV".
        iApply "HV'".
    Qed.

    Local Notation "l ↦□ v" := (logrel.pointsto_def l v)
    (at level 20,  format "l ↦□ v") : bi_scope.

    Lemma sem_typed_osum Γ e1 e2 τ :
        Γ ⊨ e1 : (TCase τ) -∗
        Γ ⊨ e2 : τ -∗
        Γ ⊨ Inj e1 e2 : TOSum.
    Proof.
        iIntros "#H1 #H2" (rho gamma) "!# #HG".
        iSpecialize ("H1" $! rho gamma with "HG"). 
        iSpecialize ("H2" $! rho gamma with "HG"). 
        (* reduce both expressions in Inj e1 e2  *)
        iApply (interp_expr_bind [InjLCtx _]).
        { iApply "H1". }
        iIntros (v1) "#HV1". 
        iApply (interp_expr_bind [InjRCtx _]).
        { iApply "H2". }
        iIntros (v2) "#HV2".
        (* expressions reduced, apply wp_value *)
        iApply wp_value.
        (* We have that v1 is a case of τ, so extract that information. *)
        iDestruct "HV1" as "[%l (%case & #typ)]"; fold interp.
        subst.
        (* Now interpret OSum *)
        iExists l. iExists v2. iExists (interp τ rho).
        iSplit.
        iPureIntro. done.
        iSplit. iApply "typ".
        iApply "HV2".
    Qed.

    Lemma points_to_agree l  P P' x : l↦□P -∗ l ↦□ P' -∗ ▷ (P x ≡ P' x).
    Proof.
        iIntros "#[%s1 (_ & _ & Q)] #[%s2 (_ & _ & Q')]".
        iApply (saved_pred_agree with "Q Q'").
    Qed.
        
 
    Lemma sem_typed_caseOf  Γ e1 e2 e3 e4 τ1 τ2 : 
        Γ ⊨ e1 : TOSum -∗ (* thing to destruct *)
        Γ ⊨ e2 : TCase τ1  -∗ (* matching on case *)
        τ1  :: Γ ⊨ e3 : τ2  -∗ (* success case *)
        Γ ⊨ e4 : τ2 -∗ (* failure case *)
        Γ ⊨ CaseOf e1 e2 e3 e4 : τ2.
    Proof.
        iIntros "#H1 #H2 #H3 #H4" (rho gamma) "!# #HG".
        iSpecialize ("H1" $! rho gamma with "HG"). 
        iSpecialize ("H2" $! rho gamma with "HG").
        iSpecialize ("H4" $! rho gamma with "HG").
        (* evaluate OSum and Case *)
        iApply (interp_expr_bind [CaseOfCtxOSUM _ _ _]).
        { iApply "H1". }
        iIntros (v1) "#HV1". 
        iApply (interp_expr_bind [CaseOfCtxInj  _ _ _]).
        { iApply "H2". }
        iIntros (v2) "#HV2".
        (* The values of OSum and Case both hold locations, 
            dispatch redution rules based on the decidable equality of locations *)
        iDestruct "HV1" as "[%l [%osumVal [%P (%inj & #prf1 & #typ)]]]".
        iDestruct "HV2" as "[%l' (%case & #prf2)]".
        subst.
        fold interp.
        (* have
            prf1 : l↦□P
            prf2 : l'↦□⟦ τ1 ⟧ rho
            typ : P osumVal

            in the case that l and l' are equal...
            then P should be equal to interp t1 rho..
        *)
        destruct (decide (l = l')) as [|Hneq]. subst.
        {
            (*      l'↦□P 
                AND 
                    l'↦□⟦ τ1 ⟧ rho 
                IMPLIES
                    ▷ (P osumVal ≡ ⟦ τ1 ⟧ rho osumVal) *)
            iPoseProof (points_to_agree _ _ _ osumVal with "prf1 prf2") as "prf".
            (* Now we can take a base step, CaseOfTrue  *)
            iApply wp_pure_step_later ; try done. 
            (* handle the later modality in goal and hypotheis *)
            iIntros "!> _". 
            fold of_val.
            (* simplify substitutions using autosubst  *)
            asimpl.
            (* now we can use our hypothesis about e3 *)
            iApply ("H3" $! (rho)(osumVal :: gamma)) .
            (* now we just have to proe the environment interpretation *)
            iApply interp_env_cons.
            iSplit.
            2:{ iApply "HG". }
            (* use the fact that 
                P osumVal ≡ ⟦ τ1 ⟧ rho osumVal 
            *) 
            iRewrite -"prf".
            iApply "typ".
        }
        iApply wp_pure_step_later.
        {
            apply wp_case_nomatch . - unfold AsVal. exists osumVal. reflexivity.
            - exact Hneq.
        } eauto.  iIntros "!> _".
        iApply "H4".
    Qed.
(* 
        Lemma wp_new e v t : 
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
        { apply to_of_val. }
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
    Qed. *)

    (* need a Wp lemma about allocation and fresh names *)
    Lemma sem_typed_new Γ e τ1 τ2 :
        (TCase τ1) :: Γ ⊨ e : τ2 -∗
        Γ ⊨ New τ1 e : τ2.
    Proof.
        iIntros "#H1" (rho gamma) "!# #HG".
        unfold interp_expr.
        iApply wp_lift_atomic_base_step_no_fork; auto.
        iIntros (s1 n k1 k2 n') "#HStinterp".
        unfold weakestpre.state_interp; simpl; unfold state_interp.

        Check wp_bind.
        Check wp_new.
        iApply wp_wand.
        { iApply wp_new. admit. }
        simpl.
        2:{ 
        Search wp_bind.
        iApply wp_new.


        (* need a weakest precondition rule fo allocating new types.. *)


        (* reduce expression e? *)
        iApply (interp_expr_bind [NewCtx τ1]).
        { iApply "H1". }
    



(*     Lemma sep_persist (P Q : iProp Sig) { _ : Persistent P}{_ : Persistent Q} : Persistent (P ∗ Q).
    apply _.
    Qed.

 (*    Check Forall Persistent.
    Lemma bigOp_persist (xs : list (iProp Sig))(prfs : Forall Persistent xs) : Persistent ([∗] xs).
    Proof.
        induction prfs.
        - apply _.
        - unfold Persistent. simpl. iIntros "H".
        iModIntro. 
        eapply sep_persist. *)
        Check big_sepL_persistent_id.

    Check big_opL bi_sep _ _ .
(*     Notation "'[∗]' Ps" := (big_opL bi_sep (λ _ x, x) Ps%I) : bi_scope.
 *)

    Local Instance env_persist (Gamma : list type)(gamma : list val)(rho : list D) : Persistent (⟦ Gamma ⟧* rho gamma).
    Proof.
        unfold interp_env.
        eapply sep_persist.
        - apply _.
        - eapply big_sepL_persistent_id.
        Admitted.



    Check wp_value.
    Check pure_exec.

    Lemma test : ⊢  WP Unit {{ v, ⌜v = UnitV⌝ }}.
    Proof.
        iApply wp_value. done.
    Qed.

    Lemma test' : True%I  -∗ WP Unit {{ v, ⌜v = UnitV⌝ }}.
    Proof.
        iIntros.
        iApply wp_value.
        done.
    Qed.


(*     Local Instance unit_exec : PureExec True 1 Unit UnitV.
 *)    
    (* notice that without persistant predicates.. 
        we can only use the fact that gamma satisfies the interpretation in the spacial context
        go back through the persistent tutorial *)
    Lemma sem_typed_unit Γ : ⊢ Γ ⊨ Unit : TUnit.
    Proof.
        iIntros (rho gamma) "!# _" .
        unfold interp_expr.
        unfold interp.
        unfold interp_TUnit.
        simpl.
        iAssert (⌜UnitV = UnitV⌝ %I) as "%H". 
        - done.
        -
        iStopProof.
        
        apply wp_value.
        Locate wp_value.
        iStopProof.
        iStartProof.
        iApply wp_value.
        simpl.
        unfold interp_expr.
        unfold interp.
        unfold interp_TUnit.
        iAssert (⌜UnitV = UnitV⌝%I).
        iPoseProof (wp_value NotStuck empty (fun v => ⌜v = UnitV⌝%I) Unit) as "prf".
        iApply "prf".

        iApply .
        simpl.
        pose proof (wp_value).
        Locate wp_value.
        iApply wp_value'.
        eapply wp_lift_base_step.
        apply nsteps_once.
        solve_pure_exec.
        wp_pure.

        iPoseProof ()
        unfold wp.
        unfold wp'.

        Check wp_value.
        iApply wp_value.

 *)
End fund.