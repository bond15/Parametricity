From stdpp Require Import base gmap coPset tactics proof_irrel sets.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map gset_bij.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre ectx_lifting.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.OSum Require Export OSum unary_logrel.

Fixpoint env_subst (vs : list val) : var → expr :=
match vs with
| [] => ids
| v :: vs' => (of_val v) .: env_subst vs'
end.


(* definition of semantic typing *)
Definition log_typed `{logrelSig Σ} (Γ : list type) (e : expr) (τ : type) : iProp Σ :=
    (□ ∀ rho (vs : list val), ⟦ Γ ⟧* rho vs -∗ ⟦ τ ⟧ₑ rho e.[env_subst vs])%I.


Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section fund.
  
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

      Lemma sem_typed_if Γ e0 e1 e2 τ :
        Γ ⊨ e0 : TBool -∗ Γ ⊨ e1 : τ -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ If e0 e1 e2 : τ.
    Proof.
        iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ"; simpl.
        iApply (interp_expr_bind [IfCtx _ _]); first by iApply "IH1".
        iIntros (v) "#Hv /=".
        iDestruct "Hv" as ([]) "%"; subst; simpl;
        [iApply wp_pure_step_later .. ]; auto; iIntros "!> _";
            [iApply "IH2"| iApply "IH3"]; auto.
    Qed.

    Lemma sem_typed_int_binop Γ op e1 e2 :
        Γ ⊨ e1 : TInt -∗ Γ ⊨ e2 : TInt -∗ Γ ⊨ BinOp op e1 e2 : binop_res_type op.
    Proof.
        iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
        iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
        iIntros (v) "#Hv /=".
        iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
        iIntros (w) "#Hw/=".
        iDestruct "Hv" as (n) "%"; iDestruct "Hw" as (n') "%"; simplify_eq/=.
        iApply wp_pure_step_later; [done|]; iIntros "!> _". iApply wp_value.
        destruct op; simpl; try destruct Z.eq_dec;
        try destruct Z.le_dec; try destruct Z.lt_dec; eauto 10.
    Qed.


    Lemma sem_typed_Eq_binop Γ e1 e2 τ :
        Γ ⊨ e1 : τ -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ BinOp Eq e1 e2 : TBool.
    Proof.
        iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
        iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
        iIntros (v) "#Hv /=".
        iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
        iIntros (w) "#Hw/=".
        iApply wp_pure_step_later; [done|]; iIntros "!> _". iApply wp_value; eauto.
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

    Local Notation "l @ l' ↦□ v" := (unary_logrel.pointsto_def l l' v)
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

    Lemma loc_agree_L l1 l2 l3 P P'  : l1 @ l2 ↦□P -∗ l3 @ l2 ↦□ P' -∗ ⌜l1 = l3⌝.
    Proof.
         iIntros "(B1 & _) (B2 & _)".
         iPoseProof (gset_bij_own_elem_agree with "B1 B2") as "%agree".
         iPureIntro.
         rewrite agree. done.
    Qed.

    Lemma loc_agree_R l1 l2 l3 P P'  : l1 @ l2 ↦□P -∗ l1 @ l3 ↦□ P' -∗ ⌜l2 = l3⌝.
    Proof.
        iIntros "(B1 & _) (B2 & _)".
        iPoseProof (gset_bij_own_elem_agree with "B1 B2") as "%agree".
        iPureIntro.
        apply agree. done.
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
        iDestruct "HV2" as "[%l3 [%l4 (%case & #prf2)]]" ;subst ;fold interp.
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

    Lemma not_in_combine_left (l1 l2 : list loc) a b : 
        a ∉ l1 -> 
        (a , b) ∉ combine l1 l2 .
    Proof.
        unfold not. intros.
        apply elem_of_list_to_set in H1.
        apply elem_of_zip_l in H1.
        apply H0. exact H1. 
    Qed.

    Lemma not_in_combine_right (l1 l2 : list loc) a b : 
        b ∉ l2 -> 
        (a , b) ∉ combine l1 l2 .
    Proof.
        unfold not. intros.
        apply elem_of_list_to_set in H1.
        apply elem_of_zip_r in H1.
        apply H0. exact H1. 
    Qed.

    Lemma adjust_combine {A B} a b :
        a ∉ A -> 
        b ∉ B -> 
        {[(a, b)]} ∪ combine A B = combine (a :: A) (b :: B).
    Proof.
        intros.
        rewrite set_eq.
        intros (a' , b').
        split.
        - intros. 
        destruct (decide (a = a' /\ b = b')).
        {
            destruct a0; subst.
            apply elem_of_list_to_set.
            rewrite (zip_with_app pair [a'] A [b'] B eq_refl).
            constructor.
        }
         apply elem_of_list_to_set.
        pose proof (zip_with_app pair [a] A [b] B eq_refl).
        rewrite H3.
        apply elem_of_list_further.
        pose proof ( elem_of_union {[(a, b)]} (combine A B) (a' , b')).
        apply H4 in H2.
        destruct H2.
        +        assert ( (a , b) <> (a' , b')). {
            unfold not. intros. inversion H5. apply n. done.
        }
        rewrite elem_of_singleton in H2. symmetry in H2. contradiction.
        + unfold combine in H2.            
         apply elem_of_list_to_set in H2. exact H2.
        -
        intros.
        unfold combine in H2. apply elem_of_list_to_set in H2.
        simpl in H2.
        unfold combine.
        Search list_to_set.
        rewrite <- list_to_set_cons.
        apply elem_of_list_to_set. exact H2.
    Qed.


    Lemma wp_new t rho : 
        ⊢ WP (New t) {{ v,∃ l l', l @ l' ↦□(interp t rho) ∗ ⌜v = CaseV l⌝}}.
    Proof.
        iApply wp_lift_atomic_base_step_no_fork; auto;  simpl.
        iIntros (s1 _ k1  _ _) "[%L (A & #B)]".
                    (* get access to the state interpretation *)
        unfold weakestpre.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* only obligation is that we need to be able to summon a fresh name *)
(*         exact (is_fresh s1).
 *)      - (* now we need to handle the state update, 
            first bring variables into scope  *)
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep. subst ; simpl.
        (* allocated read only saved predicate *)
        iMod (saved_pred_alloc_cofinite (list_to_set L) (interp t rho) DfracDiscarded) as "[%l (%lfresh & #typ)]"; try done.
        assert (l ∉ L) as lfresh'. { rewrite elem_of_list_to_set in lfresh. exact lfresh. }

        assert (∀ b' : gname, (fresh s1, b') ∉ (combine s1 L)) as c1. {
            intros. apply not_in_combine_left. 
            apply infinite_is_fresh.
        } 

        assert (∀ a' : loc, (a', l) ∉ (combine s1 L)) as c2. {
            intros. apply not_in_combine_right. exact lfresh'.
        }        
        iPoseProof (gset_bij_own_extend (fresh s1) l c1 c2 with "A") as ">(auth & #view)".
        pose proof (@adjust_combine s1 L (fresh s1) l (infinite_is_fresh s1) lfresh') as adjustment.
        iModIntro.
        iSplit. done.
        iSplit. {
            iExists (l :: L). iSplit. {
                rewrite adjustment.
                done.
            }
            { 
                rewrite big_opL_cons.
                - iSplit.  iExists (interp t rho). iApply "typ".
                iApply "B".
            }
        }
        iExists (fresh s1). iExists l.
        iSplit. 2:{ done. }
        iSplit. done.
        done.
    Qed.

    (*  this returns the updated authoritative element AND a new view element *)
    (*  better library functions for gset_bij
     https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.gset_bij.html *)
      

    (* with the weakest precondition in hand, this is easy *)
    Lemma sem_typed_new Γ t :
        ⊢  Γ ⊨ (New t) : TCase t.
    Proof.
        iIntros (rho gamma) "!# #HG".
        iApply wp_wand.
        iApply wp_new.
        iIntros (v) "[%l [%l' (B & P)]]".
        simpl.
        iExists l. iExists l'. iSplit; done.
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
        - iApply sem_typed_int_binop; done.
        - iApply sem_typed_Eq_binop; done.
        - iApply sem_typed_pair; done.
        - iApply sem_typed_fst; done.
        - iApply sem_typed_snd; done.
        - iApply sem_typed_osum; done.
        - iApply sem_typed_caseOf; done.
        - iApply sem_typed_new; done.
        - iApply sem_typed_if; done.
        - iApply sem_typed_lam; done.
        - iApply sem_typed_letin; done.
        - iApply sem_typed_app; done.
        - iApply sem_typed_tlam; done.
        - iApply sem_typed_tapp; done.
        - iApply sem_typed_pack; done.
        - iApply sem_typed_unpack; done.
    Qed.


End fund.

(*     Check fresh.






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
        iMod (saved_pred_alloc_cofinite (list_to_set L) (interp t rho) DfracDiscarded) as "[%l (%lfresh & typ)]"; try done.
        assert (l ∉ L). { rewrite elem_of_list_to_set in lfresh. exact lfresh. }
        (* Now we just have to show that the state interpretation is preserved
          and that we have a location pointing to a predicate representing typing of t
            which we just allocated *)
        (* no forks *)
        iApply fupd_frame_l; iSplit ; try done.
        (* prove the WP post condition with "typ" *)
        iApply fupd_frame_r; iSplit. 2: { iExists l; iApply "typ". }
        (* Trickier part, showing that the state interpretation is preserved
            here we have to update our bijection of fresh names
            we have two new names "fresh s1" and "l"
            and we need to update the saved predicate map wit our newly allocated predicate
         *)
        iExists (l :: L).
        (* update the saved predicate map *)
        iApply fupd_frame_r. iSplit. 2: {
            rewrite big_opL_cons.
            - iSplit.  iExists (interp t rho). iApply "typ".
            iApply "B".
        }
        (* show update the name bijection.
            Note: this seems to be a newer camera in Iris and is missing some useful lemmas
            Clean this up and add to their library
         *)
        (* first step, show that "(fresh s1, l)" is a new element of (combine s1 L) *)

        Check gset_bij_auth_extend (fresh s1) l.
        assert (∀ a' : loc, (a', l) ∉ (combine s1 L)). {
            intros. apply not_in_combine_right. exact H0.
        }        
        assert (∀ b' : gname, (fresh s1, b') ∉ (combine s1 L)). {
            intros. apply not_in_combine_left. 
            apply infinite_is_fresh.
        } 
        (* now we can derive a valid update ~~> *) 
        pose proof (gset_bij_auth_extend (fresh s1)l H2 H1).
        (* fix the update target with the correct set *)
        rewrite (@adjust_combine s1 L (fresh s1) l (infinite_is_fresh s1) H0) in H3.
        (* Finally.. with the update in hand, we can update the cell "new_set" *) 
(*         iMod (own_update name_set _ _ H3 with "A") as "goal".
        done. *)
    
    

(*     Lemma viewfinder a b a' b': ⊢
        own name_set (gset_bij_auth (DfracOwn 1) {[ (a , b) ; (a' , b')]}) ==∗  
        own name_set (op (gset_bij_auth (DfracOwn 1) {[ (a , b) ; (a' , b')]}) (gset_bij_elem a' b')).
    Proof.
        iIntros "H".
        unfold gset_bij_auth. unfold gset_bij_elem.

Check  gset_bij_own_extend.
    Lemma viewfinder a b a' b': ⊢
        own name_set (gset_bij_auth (DfracOwn 1) {[ (a , b) ; (a' , b')]}) ==∗  
        own name_set (gset_bij_elem a' b').
        (* own name_set (●V {[(a, b); (a', b')]} ⋅ ◯V {[(a, b); (a', b')]})
            --------------------------------------∗
            |==> own name_set (◯V {[(a', b')]}) *)
    Proof.
        iIntros "H".
        unfold gset_bij_auth. unfold gset_bij_elem.
        Check own_op.
        Check view_update_dealloc _ _ _ _ _ .
        Check own_update name_set _ _  (view_update_dealloc _  _ _ _ _).
        iMod (own_update name_set _ _  (view_update_dealloc _  _ _ _ _)).
        iApply (own_op name_set with "H") .
        Check own_op name_set _ _(_ : own name_set (●V {[(a, b); (a', b')]} ⋅ ◯V {[(a, b); (a', b')]})).
        iMod (own_op name_set _ _ with "H") as "huh".  *)



    Lemma gset_bijective_extend'        
        (A : gset loc)
        (B : gset loc) a b :
        gset_bijective (gset_cprod A B) →
        a ∉ A ->
        b ∉ B ->
        (∀ b', (a, b') ∉ (gset_cprod (A ∪ {[a]}) (B ∪ {[b]}))) →
        (∀ a', (a', b) ∉ (gset_cprod (A ∪ {[a]}) (B ∪ {[b]}))) →
        gset_bijective (gset_cprod (A ∪ {[a]}) (B ∪ {[b]})).
    Proof. rewrite /gset_bijective. set_solver. Qed.

        Section gset_bij_view_rel.
            Context `{Countable A, Countable B}.
            Implicit Types (bijL : gset (A * B)) (L : gsetUR (A * B)).
            Local Lemma gset_bij_view_rel_iff n bijL L :
            gset_bij_view_rel n bijL L ↔ L ⊆ bijL ∧ gset_bijective bijL.
          Proof. done. Qed.
        End  gset_bij_view_rel.


    Lemma gset_bij_auth_extend (A : gset loc) (B : gset loc) a b :
        gset_bijective (gset_cprod A B) →
        a ∉ A ->
        b ∉ B ->
        gset_bij_auth (DfracOwn 1) (gset_cprod A B) ~~> gset_bij_auth (DfracOwn 1) (gset_cprod (A ∪ {[a]}) (B ∪ {[b]})).
    Proof.
        intros.
        apply view_update. intros.

        rewrite gset_bij_view_rel_iff.

 *)


  (*   Lemma modifyBijection 
        (A : gset loc)
        (B : gset loc)
        (a' b' : loc)
        (afresh : a' ∉ A)
        (bfresh : b' ∉ B)
        (H : gset_bijective ({[(a', b')]} ∪ gset_cprod A B)) : 
        gset_bijective (gset_cprod (A ∪ {[a']}) (B ∪ {[b']})).
    Proof.
        set (S := gset_cprod A B) in *.
        set (S1 := {[(a', b')]} ∪ S) in *.
        set (S2 := gset_cprod (A ∪ {[a']}) (B ∪ {[b']})) in *.
        (* The original set S is A * B 
        *)
        assert ((a', b')  ∈ S1) by set_solver.
        assert ((a', b')  ∈ S2) by set_solver.
        assert (gset_bijective S). {
            eapply subseteq_gset_bijective.
            exact H.
            set_solver.
        }
        apply gset_bijective_extend'.
        exact H2.
        exact afresh.
        exact bfresh.
        - unfold not. intros b'' Hb''. 
        (* case on b'' in B *)
        apply elem_of_gset_cprod in Hb''; simpl in Hb''; destruct Hb''.
        

        destruct (decide ((a', b'') ∈ S1)).
        {
            Check gset_bijective_eq_iff S1 a' a' b' b'' H H0 e.
            apply elem_of_gset_cprod in Hb''; simpl in Hb''; destruct Hb''.


        }

        (* determine if an arbitrary element, (a,b), of S2 is in S
            If it is, '
                then use the bijeciton of S
            else
                either (a = a') or (b = b') by elem_of_gset_cprod
                then what..? use the bijection on S1?
        *)
        unfold gset_bijective; intros.
        destruct (decide ((a, b) ∈ S)).
        - split. {
            (* on b 
                if b'' is in B, 
                    then b'' = b via bijection on S
                else
                    b'' = b' 
                    which is not in S
            *)
            intros b'' Hb''.
            destruct (decide (b'' ∈ B)).
            {
                assert ((a, b'') ∈ S). {
                    set_solver.
                }
                pose proof (gset_bijective_eq_iff S a a b'' b H2  H4 e).
                rewrite <-H5. reflexivity. 
            }
            (* b'' = b' ... so what *)
            apply elem_of_gset_cprod in Hb''; simpl in Hb''.
            assert (b'' = b'). { set_solver. } subst.
            apply elem_of_gset_cprod in e; simpl in e. destruct e.
            apply elem_of_gset_cprod in H3; simpl in H3.

        }



        (* we have a bijection on S and S1  
          Either an arbitrary element (a,b) of S2 is in S or it 
        *)
        unfold gset_bijective.



        (* we have to define the bijection.. on any arbitrary pair (a,b) in S2 *)
        intros.
        (* S1 is a subset of S2
        Decide if the arbitrary element (a,b) of S2 is in S1
        If it is, just use the bijection in S1 *)
        destruct (decide ((a, b) ∈ S1)).
        - (* if it is in S1, just use S1's bijection *)
        split. 
        + intros b'' Hb''.
        (* is b'' could be in B or {[b']} .. case on this *)
        destruct (decide (b'' = b')). 
        {
            (* b'' = b  then we use the bijection in S*)
        } 
        Check gset_bijective_eq_iff S1.
        epose proof (gset_bijective_eq_iff S1 a a' b b' H e H0).

        (* then we have two goals.. the proof for both will be similar.. so start with one *)
        split.
        - (* for b in (a , b) in S2... consider if it is the fresh element b' or not *)
        intros b'' Hb''.
        destruct (decide (b'' = b')).
        + subst.  
        (* if it is the fresh element. we want to associate it with a' 
            so apply the fact that S1 := {[(a', b')]} ∪ S  is bijective "in reverse"

        *)
        pose proof (H a' b' H0) as (d ,_).
        specialize d with b. symmetry. apply d.

        + subst.

        apply elem_of_gset_cprod in H3; simpl in H3.
        - intros b'' Hb''.
        destruct (decide (b = b')).
        + subst. unfold gset_bijective in H.
        pose proof (H a' b' H0). 
        destruct H4.
        apply H4.
        
         apply H with (a := a')(b := b'). exact H0. 



        unfold gset_bijective in *.
        intros.
        split.
        - intros b'' Hb''.
        apply elem_of_gset_cprod  in H0; simpl in H0;
        apply elem_of_gset_cprod  in Hb'' ; simpl in Hb''.
        pose proof (prf a' b').
        assert ((a', b) ∈ {[(a', b')]} ∪ gset_cprod A B) by set_solver.
        apply H1 in H2. destruct H2. pose proof (H2 b'').
        apply H4.

        instantiate 
        set_solver.
        eapply subseteq_gset_bijective.

        set (S1 := gset_cprod A B) in *.
        set (S2 := {[(a', b')]} ∪ S1).
        assert (gset_bijective S2). {
            apply gset_bijective_extend.
            exact prf.
        }

   (*      remember (fresh A) as a' in *.
        remember (fresh B) as b' in *. *)

(*         set (S1 := gset_cprod A B) in *.
        set (S2 := {[(a', b')]} ∪ S1). *)
        Check is_fresh a'.
        unfold gset_bijective in *. set_solver.
        apply subseteq_gset_bijective with S2.

        set ((a'b' : gset (loc * loc  )):= {[(a' , b')]}) in *. 
        
 *)