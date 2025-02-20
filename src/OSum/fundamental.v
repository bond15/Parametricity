From stdpp Require Import base gmap coPset tactics proof_irrel sets.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
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


(* definition of semantic typing *)
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

    Lemma sem_typed_int Γ (n : Z) : ⊢ Γ ⊨ #n n : TInt.
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

    Import uPred.

    Lemma interp_env_ren Δ (Γ : list type) (vs : list val) τi :
        ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vs ⊣⊢ ⟦ Γ ⟧* Δ vs.
    Proof.
        apply sep_proper; [apply pure_proper; by rewrite length_fmap|].
        revert Δ vs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
        apply sep_proper; auto. rewrite (interp_weaken [] [τi] Δ). eauto.
    Qed.

    Lemma sem_typed_tlam Γ e τ : (subst (ren (+1)) <$> Γ) ⊨ e : τ -∗ Γ ⊨ TLam e : TForall τ.
    Proof.
        iIntros "#IH" (Δ vs) "!# #HΓ /=".
        iApply wp_value; simpl.
        iModIntro; iIntros (τi). iApply wp_pure_step_later; auto. iIntros "!> _".
        iApply "IH". by iApply interp_env_ren.
    Qed.

    Lemma sem_typed_tapp Γ e τ τ' : Γ ⊨ e : TForall τ -∗ Γ ⊨ TApp e : τ.[τ'/].
    Proof.
        iIntros "#IH" (Δ vs) "!# #HΓ /=".
        iApply (interp_expr_bind [TAppCtx]); first by iApply "IH".
        iIntros (v) "#Hv /=". fold interp.
        iApply wp_wand_r; iSplitL;
        [iApply ("Hv" $! (⟦ τ' ⟧ Δ)); iPureIntro; apply _|]; cbn.
        iIntros (w) "?". by iApply interp_subst.
    Qed.

    Lemma sem_typed_letin Γ e1 e2 τ1 τ2 : Γ ⊨ e1 : τ1 -∗ τ1 :: Γ ⊨ e2 : τ2 -∗ Γ ⊨ LetIn e1 e2: τ2.
    Proof.
        iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ"; simpl.
        iApply (interp_expr_bind [LetInCtx _]); first by iApply "IH1".
        iIntros (v) "#Hv /=".
        iDestruct (interp_env_length with "HΓ") as %?.
        iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
        asimpl. iApply ("IH2" $! Δ (v :: vs)).
        iApply interp_env_cons; iSplit; eauto.
    Qed.

    (* something off with existentials, check these. *)
    Lemma sem_typed_pack Γ e τ τ' : Γ ⊨ e : τ.[τ'/] -∗ Γ ⊨ Pack e : TExist τ.
    Proof.
        iIntros "#IH" (Δ vs) "!##HΓ /=".
        iApply (interp_expr_bind [PackCtx]); first by iApply "IH".
        iIntros (v) "#Hv /=".
        iApply wp_value.
        rewrite -interp_subst.
        iExists (interp _ Δ), _. fold interp. iSplit. done.
        (* huh..?  *) admit.
    Admitted.

    Lemma sem_typed_unpack Γ e1 e2 τ τ' :
        Γ ⊨ e1 : TExist τ -∗
        τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 : τ'.[ren (+1)]  -∗
        Γ ⊨ UnpackIn e1 e2 : τ'.
    Proof.
        iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
        iApply (interp_expr_bind [UnpackInCtx _]); first by iApply "IH1".
        iIntros (v) "#Hv /=".
        iDestruct "Hv" as (τi w ->) "#Hw"; simpl.
        iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
        asimpl.
        iApply wp_wand_r; iSplitL.
        { iApply ("IH2" $! (τi :: Δ) (w :: vs) with "[]").
        iApply interp_env_cons. iSplit. admit. 
        iApply interp_env_ren; done. }
        iIntros (u) "Hu".
        iApply (interp_weaken [] [_]); done.
    Admitted.

    (* ------------- NEW stuff ------------------------ *)

    Local Notation "l @ l' ↦□ v" := (logrel.pointsto_def l l' v)
    (at level 20,  format "l @ l' ↦□ v") : bi_scope. 

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
        iDestruct "HV1" as "[%l (%l' & %case & #typ)]"; fold interp ; subst.
        (* Now interpret OSum *)
        iExists l. iExists l'. iExists v2. iExists (interp τ rho).
        iSplit.
        iPureIntro. done.
        iSplit. iApply "typ".
        iApply "HV2".
    Qed.

    Lemma points_to_agree l l' l'' P P' x : l'' @ l' ↦□P -∗ l @ l' ↦□ P' -∗ ▷ (P x ≡ P' x).
    Proof.
        iIntros "(_ & Q) (_ & Q')".
        iApply (saved_pred_agree with "Q Q'").
    Qed. 

    (* hack and slash, clean this *)
    Lemma loc_agree_L l1 l2 l3 P P'  : l1 @ l2 ↦□P -∗ l3 @ l2 ↦□ P' -∗ ⌜l1 = l3⌝.
    Proof.
         iIntros "(B1 & _) (B2 & _)".
         Check  gset_bij_elem_agree.
         Check own_op.
         iStopProof.
         iIntros "P".
         iPoseProof (own_op name_set _ _ with "P")as "foo".
         iPoseProof (own_valid with "foo") as "%bar".
         apply gset_bij_elem_agree in bar.
         destruct bar.
         pose proof (H1 eq_refl).
         iPureIntro. done.
    Qed.

    Lemma loc_agree_R l1 l2 l3 P P'  : l1 @ l2 ↦□P -∗ l1 @ l3 ↦□ P' -∗ ⌜l2 = l3⌝.
    Proof.
         iIntros "(B1 & _) (B2 & _)".
         Check  gset_bij_elem_agree.
         Check own_op.
         iStopProof.
         iIntros "P".
         iPoseProof (own_op name_set _ _ with "P")as "foo".
         iPoseProof (own_valid with "foo") as "%bar".
         apply gset_bij_elem_agree in bar.
         destruct bar.
         pose proof (H0 eq_refl).
         iPureIntro. done.
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
        iDestruct "HV1" as "[%l1 [%l2 [%osumVal [%P (%inj & #prf1 & #typ)]]]]".
        iDestruct "HV2" as "[%l3 [%l4 (%case & #prf2)]]".
        subst.
        fold interp.
        (* have
            prf1 : l1@l2↦□P
            prf2 : l3@l4↦□⟦ τ1 ⟧ rho
            typ : P osumVal

            in the case that l1 and l3 are equal...
            then P should be equal to interp t1 rho..
        *)
        destruct (decide (l1 = l3)) as [|Hneq]. subst.
        {
            (*      l3@l4↦□P
                AND 
                    l3@l4↦□⟦ τ1 ⟧ rho
                IMPLIES
                    ▷ (P osumVal ≡ ⟦ τ1 ⟧ rho osumVal) *)
            Check points_to_agree.
            iPoseProof (loc_agree_R with "prf1 prf2") as "%eqd"; subst.
            iPoseProof (points_to_agree _ _ _ _ _ osumVal with "prf1 prf2") as "prf".
            (* Now we can take a base step, CaseOfTrue  *)
            iApply wp_pure_step_later ; try done ; fold of_val.
            (* handle the later modality in goal and hypotheis *)
            iIntros "!> _". 
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
        (* here the cases in the match are not equal, goes to default case *)
        iApply wp_pure_step_later.
        (* need to fix the pure exec instance to clean this up *)
        {
            apply wp_case_nomatch . - unfold AsVal. exists osumVal. reflexivity.
            - exact Hneq.
        } eauto.  iIntros "!> _".
        (* just apply the default case we got via intros *)
        iApply "H4".
    Qed.

    Local Notation "l ↦ P" := (saved_pred_own l DfracDiscarded P)
    (at level 20,  format "l ↦ P") : bi_scope.

    (* proved, but not strong enough, 
        need to mention the other location in bijection with l'
        and that ⌜v = CaseV l⌝*)
    Lemma wp_new t rho : 
        ⊢ WP (New t) {{ v, ∃ l', l' ↦ (interp t rho)}}.
    Proof.
        iApply wp_lift_atomic_base_step_no_fork; auto.
        iIntros (s1 n k1 k2 n') "[%L (A & #B)]".
        (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* now we need to handle the state update, 
            first bring variables into scope  *)
        -
        iModIntro; iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep; subst ; simpl.
        (* here we allocate a new predicate representing the typing of t *)
        iMod (saved_pred_alloc_cofinite L (interp t rho) DfracDiscarded) as "[%l (%lfresh & typ)]"; try done.
        (* Now we just have to show that the state interpretation is preserved
          and that we have a location pointing to a predicate representing typing of t
            which we just allocated *)
        (* no forks *)
        iApply fupd_frame_l; iSplit ; try done.
        (* prove the WP post condition with "typ" *)
        iApply fupd_frame_r. iSplit. 2: { iExists l; iApply "typ". }
        (* Trickier part, showing that the state interpretation is preserved
            here we have to update our bijection of fresh names
            we have two new names "fresh s1" and "l"
            and we need to update the saved predicate map wit our newly allocated predicate
         *)
        iExists (L ∪ {[l]}).
        (* update the saved predicate map *)
        iApply fupd_frame_r. iSplit. 2: {
            iApply big_opS_union.
            - set_solver.
            - iSplit. {iApply "B". }
            iApply big_opS_singleton . iExists (interp t rho). iApply "typ".
        }
        (* show update the name bijection.
            Note: this seems to be a newer camera in Iris and is missing some useful lemmas
            Clean this up and add to their library
         *)
        (* first step, show that "(fresh s1, l)" is a new element of (gset_cprod s1 L) *)
        assert (∀ b' : gname, (fresh s1, b') ∉ (gset_cprod s1 L)). {
            intros. rewrite elem_of_gset_cprod. unfold not. intros. destruct H0. simpl in H0.
            pose proof (is_fresh s1). contradiction.
        } 
        assert (∀ a' : loc, (a', l) ∉ (gset_cprod s1 L)). {
            intros. rewrite elem_of_gset_cprod. unfold not. intros. destruct H1. simpl in H2. contradiction. 
        }
        (* now we can derive a valid update ~~> *) 
        pose proof (gset_bij_auth_extend (fresh s1)l H0 H1).
        (* The update is for a set that is obviously equal.. but we have to prove this *)
        assert ({[(fresh s1, l)]} ∪ gset_cprod s1 L = gset_cprod (s1 ∪ {[fresh s1]}) (L ∪ {[l]})). {
          (* obvious, but annoying to prove  *) admit.
          (*   apply set_eq. apply elem_of_gset_cprod *) }
        (* fix the update target with the correct set *)
        rewrite H3 in H2.
        (* Finally.. with the update in hand, we can update the cell "new_set" *) 
        iMod (own_update name_set _ _ H2 with "A") as "goal".
        done.
        (* proof is finished modulo dumb proof that two obviously equal sets are equal *)
    Admitted.

    (* Need to enhance the WP of new to prove semantic typing
        specifically we need to surface the fact that there is a bijection on locations 
        and the case returned by New is in bijection with a new predicate
     *)
    Lemma wp_new' t rho : 
        ⊢ WP (New t) {{ v,∃ l l', l @ l' ↦□(interp t rho) ∗ ⌜v = CaseV l⌝}}.
    Proof.
        iApply wp_lift_atomic_base_step_no_fork; auto.
        iIntros (s1 n k1 k2 n') "[%L (A & #B)]".
                    (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* only obligation is that we need to be able to summon a fresh name *)
(*         exact (is_fresh s1).
 *)        - (* now we need to handle the state update, 
            first bring variables into scope  *)
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep. subst ; simpl.
        iMod (saved_pred_alloc_cofinite L (interp t rho) DfracDiscarded) as "[%l (%lfresh & #typ)]"; try done.

        iApply fupd_frame_l; iSplit ; try done.
        iApply fupd_frame_l; iSplitL "A".
        (* ah, the view camera for the bijection is a bit more annoying
            need to be careful how those resources are split 
        
            Should be doable.. just more annoying
            *)
         Admitted.


    (* with the weakes precondition in hand, this is easy *)
    Lemma sem_typed_new Γ t :
        ⊢  Γ ⊨ (New t) : TCase t.
    Proof.
        iIntros (rho gamma) "!# #HG".
        iApply wp_wand.
        iApply wp_new'.
        iIntros (v) "[%l [%l' (B & P)]]".
        simpl.
        iExists l. iExists l'. iSplit.
        - iApply "P".
        - iApply "B".
    Qed.

    (* by induction on syntactic typing  *)
    Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e : τ.
    Proof.
        intros synTyp.
        induction synTyp.
        - iApply sem_typed_var; done.
        - iApply sem_typed_unit; done.
        - iApply sem_typed_int; done.
        - iApply sem_typed_bool; done.
        - admit. (* sem_typed_int_binop *)
        - admit.  (* sem_typed_Eq_binop *)
        - iApply sem_typed_pair; done.
        - iApply sem_typed_fst; done.
        - iApply sem_typed_snd; done.
        - iApply sem_typed_osum; done.
        - iApply sem_typed_caseOf; done.
        - iApply sem_typed_new; done.
        - admit. (* sem_typed_if *)
        - iApply sem_typed_lam; done.
        - iApply sem_typed_letin; done.
        - iApply sem_typed_app; done.
        - iApply sem_typed_tlam; done.
        - iApply sem_typed_tapp; done.
        - iApply sem_typed_pack; done.
        - iApply sem_typed_unpack; done.
    Admitted.


End fund.


 



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


(*     
    Lemma pred_infinite (s : state): pred_infinite (fun (l : loc) =>  l = (fresh s)).
    Proof.
        Check sigT (elem_of s).
        unfold pred_infinite.

        apply (pred_infinite_set (C:=sigT (elem_of s) )).
        Check infinite_is_fresh.
        intros X.
        Abort. *)
          
    Lemma newPred (P : iProp Σ) (s : state): ⊢ |==> P.
    Proof.
        iMod (saved_pred_alloc_cofinite s (fun (v : val) => True%I) DfracDiscarded) as "[%l (%fresh & #P)]".
        - done. 
        - 
    Abort.

        Check own_eq.
        Check own_equal.
        rewrite <- H3.
        iMod (own_update name_set _ _ H2).
        Check own_update.
        iMod 
        assert ({[(fresh s1, l)]} ∪ gset_cprod s1 L = gset_cprod (s1 ∪ {[fresh s1]}) (L ∪ {[l]})). {
            admit.
        } 
        iRewrite H3.
        Check gset_bij_auth_extend (fresh s1)l.



        Check @big_opS_op.
        Check big_opS_op (fun (p : loc * loc) => ⌜p.1 ∈ s1⌝%I)(fun (p : loc * loc) => (∃ P : wp_rules.D, p.2 ↦ P)%I) L.





        pose proof (big_opS_op (fun (p : loc * loc) => ⌜p.1 ∈ s1⌝%I)(fun (p : loc * loc) => (∃ P : wp_rules.D, p.2 ↦ P)%I) L). 
        iRewrite -(H0 with "B").
        iApply (big_opS_op (fun (p : loc * loc) => ⌜p.1 ∈ s1⌝%I)(fun (p : loc * loc) => (∃ P : wp_rules.D, p.2 ↦ P)%I) L with "B") .
        
        Check gset_bij_auth_extend (fresh s1)l.
        assert (∀ b' : gname, (fresh s1, b') ∉ L).
        {
            intros. set_solver.
        }

        iAssert (∀ b' : gname, (fresh s1, b') ∉ L)%I as "Hyp1".


        iApply fupd_exist.
        iExists L.
        iModIntro.
        iSplit. iApply "A".
        

        

        iModIntro.
        iSplit.
        + done.
        + iSplit.
        2: { iExists l. iApply "typ". }
        iDestruct "HStinterp" as "[%L (A & #B)]".
        iApply fupd_frame_l.
        i
        Check is_fresh.
        "[%l' (%fresh & #P)]"; try done.




        (*  Show that we can extend state s1 with a fresh location *)
        assert (s1 ~~> (s1 ∪ {[fresh s1]})) as update by done.
        (* now how do we use that update to modify name_set 
            using own_update? 
          first, we only need the ownership under the update modality
            so use the frame rules to shove things around  
        *)
        iApply fupd_frame_l.
        iSplit. { done. }
        iMod (own_update name_set s1 _ update with "HStinterp") as "#s1'".
        iMod (saved_pred_alloc_cofinite s1 (interp t rho) DfracDiscarded) as "[%l' (%fresh & #P)]".
        done.
        iApply fupd_frame_r.
        (* here we need to make a choice w.r.t. the spacial context
           We dont need HPhi to prove ownership, but we do need it to show
           that the post condition holds, so push it to that goal  *)
        iSplitL "HStinterp".
        (* now we can update the name_set *)
        {
            iMod (own_update name_set s1 _ update with "HStinterp") as "#s1'".
            iMod (saved_pred_alloc_cofinite s1 (interp t rho) DfracDiscarded) as "[%l' (%fresh & #P)]".
            done.
            iModIntro ; done. 
        }
        rewrite H2. done.



    Lemma wp_new t e v s l rho : 
        {{{ own name_set s ∗ ⌜¬ l ∈ s /\ IntoVal (e .[Case l/]) v ⌝ }}}
            (New t) 
        {{{ v, RET v ; ∃ l, l ↦ (interp t rho)}}}.
    Proof.
        iIntros (phi) "(#H1 & %H2 & %H3) H4".

        iApply wp_lift_atomic_base_step_no_fork; auto.
                iIntros (s1 n k1 k2 n') "#HStinterp".
        (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        { unfold IntoVal in H3. simpl in H3. rewrite <- H3.  apply to_of_val. }
        exact H2.


        iApply wp_lift_pure_step_no_fork.
        - intros s. unfold reducible. 
        exists []. exists (e.[Case (fresh s)/]). exists (s ∪ {[fresh s]}). exists [].
        simpl. econstructor. reflexivity.

        unfold prim_step.
        repeat eexists.
        iApply wp_step_fupd.
        - done.
        - done.
        iApply wp_unfold.
        simpl.
        red. simpl. red. simpl.
        unfold wp. unfold wp'. simpl. red. red. red.


(* 
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  ∃ γ. apply not_elem_of_union, is_fresh.
Qed.
 *)

(* 
    Lemma pInf (s : state): pred_infinite (fun g => g = (fresh s)).
    Proof.
        apply (pred_infinite_set (C:=gset gname)).
          intros E. set (γ := fresh (s ∪ E)).
        exists γ. split. set_solver. apply not_elem_of_union.
        
        apply not_elem_of_union, is_fresh.
        intros. exists (fresh s). split. reflexivity. apply not_elem_of_union.
 *)
    Check fresh.
    Lemma wp_new t (s : state) e v: 
        {{{ own name_set s ∗ ⌜IntoVal (e .[Case (fresh s)/]) v ⌝ }}}
            (New t e) 
        {{{ v', RET v' ; True}}}.
    Proof.
        iIntros (phi) "(#H1 & %H2) H3".
        iApply wp_lift_atomic_base_step_no_fork; auto.
                iIntros (s1 n k1 k2 n') "#HStinterp".
        (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        { unfold IntoVal in H2. simpl in H2. subst. simpl. apply to_of_val. }

    Lemma wp_new t (s : state) e v: 
        {{{ own name_set s ∗ (∃ l, ⌜l ∈ s  /\ IntoVal (e .[Case (fresh s)/]) v ⌝) }}}
            (New t e) 
        {{{ v, RET v ; True}}}.


(* 
    Lemma wp_new t e v l rho : 
        IntoVal (e.[Case l/]) v ->
        ⊢ WP (New t e) {{ v, ∃ l, l ↦ (interp t rho)}}.
    Proof. *)
        intros ev. 
        iStartProof.
(*         iApply wp_fupd.
 *)        (* break into the guts WP using using the language lifting *)
        iApply wp_lift_atomic_base_step_no_fork; auto.
        iIntros (s1 n k1 k2 n') "#HStinterp".
        (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS. 
        { 
            unfold IntoVal in ev. rewrite <- ev. simpl. apply to_of_val. }
    Abort.

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

        Locate wp.
        Check interp τ1 rho. 
        iAssert ()
        unfold interp_expr.
        unfold interp_env. simpl.
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
   

    Check encode.
    Check decode.
    Locate decode.
    Check encode_nat (9%positive).
    Eval vm_compute in  encode_nat (9%positive). (* evaluates to 8 : nat *)

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