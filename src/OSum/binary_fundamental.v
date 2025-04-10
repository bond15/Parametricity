From stdpp Require Import base gmap coPset tactics proof_irrel sets.

From iris.base_logic Require Import base_logic invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map gset_bij.
From iris.algebra Require Import cmra cofe_solver gset gmap_view excl gset_bij.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre ectx_lifting ectx_language.
Require Import Autosubst.Autosubst.

From MyProject.src.OSum Require Export OSum binary_logrel binary_rules.

Fixpoint env_subst (vs : list val) : var → expr :=
match vs with
| [] => ids
| v :: vs' => (of_val v) .: env_subst vs'
end.

Section bin_log_def.
    Context `{logrelSig Σ, configSpec Σ}.

    Definition bin_log_related (Γ : list type)(e e' : expr)(t : type) : iProp Σ := 
        (□ ∀ rho ws, 
            spec_ctx ∧ ⟦ Γ ⟧* rho ws -∗  
            ⟦ t ⟧ₑ rho (e.[env_subst (ws.*1)], e'.[env_subst (ws.*2)]))%I.

    
    Global Instance: ∀ Γ e e' τ, Persistent (bin_log_related Γ e e' τ).
    Proof. rewrite/bin_log_related /=. apply _. Qed.
      
End bin_log_def.
      
Notation "Γ ⊨ e '≤log≤' e' : τ" :=
    (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).
      
Section fundamental.
    Context `{logrelSig Σ, configSpec Σ}.

    Lemma bin_log_rel_unit Γ : ⊢ Γ ⊨ Unit ≤log≤ Unit : TUnit.
    Proof.
        (* unpack binary logical relation definition *)
        iIntros (rho ws).
        iModIntro.
        iIntros "(#Hs & #HGam)".
        (* unpack interpretation of expressions *)
        unfold interp_expr; asimpl.
        iIntros (K) "Hspec". 
        (* Unit is a value *)
        iApply wp_value.
        iExists UnitV.
        iSplit.
        - iApply "Hspec".
        - done.
    Qed.

    Lemma bin_log_rel_bool Γ b : ⊢ Γ ⊨ Bool b ≤log≤ Bool b : TBool.
    Proof.
        iIntros (rho ws) "!#(#Hs & #Hgam)".
        unfold interp_expr; asimpl.
        iIntros (K) "Hspec".
        iApply wp_value.
        iExists (BoolV b).
        iSplit.
        - iApply "Hspec".
        - iExists b. done.
    Qed.
        
    Lemma bin_log_rel_int Γ n : ⊢ Γ ⊨ Int n ≤log≤ Int n : TInt.
    Proof.
        iIntros (rho ws) "!#(#Hs & #Hgam)".
        unfold interp_expr; asimpl.
        iIntros (k) "Hspec".
        iApply wp_value.
        iExists (IntV n).
        iSplit.
        - iApply "Hspec".
        - iExists n. done.
    Qed.

    Lemma interp_expr_bind KK ee Δ τ τ' :
    ⟦ τ ⟧ₑ Δ ee -∗
    (∀ vv, ⟦ τ ⟧ Δ vv -∗ ⟦ τ' ⟧ₑ Δ (fill KK.1 (of_val vv.1), fill KK.2 (of_val vv.2))) -∗
    ⟦ τ' ⟧ₑ Δ (fill KK.1 ee.1, fill KK.2 ee.2).
  Proof.
    iIntros "He HK" (Z) "Hj /=".
    iSpecialize ("He" with "[Hj]"); first by rewrite -fill_app; iFrame.
    iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (?); iDestruct 1 as (?) "[? #?]".
    iApply ("HK" $! (_, _)); [done| rewrite /= fill_app //].
  Qed.

  Lemma interp_expr_bind' K K' e e' Δ τ τ' :
    ⟦ τ ⟧ₑ Δ (e, e') -∗
    (∀ vv, ⟦ τ ⟧ Δ vv -∗ ⟦ τ' ⟧ₑ Δ (fill K (of_val vv.1), fill K' (of_val vv.2))) -∗
    ⟦ τ' ⟧ₑ Δ (fill K e, fill K' e').
  Proof. iApply (interp_expr_bind (_, _) (_, _)). Qed.

  Lemma interp_expr_val vv rho t : ⟦ t ⟧ rho vv -∗ ⟦ t ⟧ₑ rho (of_val vv.1, of_val vv.2).
  Proof. destruct vv. iIntros "?" (?) "?". iApply wp_value. iExists _. iFrame. Qed.

    Lemma bin_log_rel_pair Γ t1 t2 e1 e2 e3 e4 :
        Γ ⊨ e1 ≤log≤ e2 : t1 -∗
        Γ ⊨ e3 ≤log≤ e4 : t2 -∗
        Γ ⊨ Pair e1 e3 ≤log≤ Pair e2 e4 : TProd t1 t2.
    Proof.
        (* assumptions *)
        iIntros "#Hp1 #Hp2" (rho ws) "!#(#Hs & #Hgam)" .
        iIntros (K) "Hspec". 
        (* specialize Hp1 and Hp2 *)
        iSpecialize ("Hp1" $! rho ws with "[# $Hs  $Hgam]").
        iSpecialize ("Hp2" $! rho ws with "[# $Hs  $Hgam]").
        (* reduce the pair to values 
           first the left side *)
        iApply (interp_expr_bind' [PairLCtx _] [PairLCtx _]).
        1:{ iApply "Hp1". }
        2:{ asimpl. iApply "Hspec". }
        (* now the right side *)
        iIntros ([v1 v2]) "#Hv12".
        iApply (interp_expr_bind' [PairRCtx _] [PairRCtx _]).
        { iApply "Hp2". }
        iIntros ([v3 v4]) "#Hv34".
        (* now we have a value *)
        iApply (interp_expr_val (PairV _ _, PairV _ _)).
        (* use the value interpretation of products *)
        iExists (v1 , v2). iExists (v3 , v4). fold interp.
        (* and we are done *)
        repeat iSplit ; done.
    Qed.

    (* pick up to_of_val in eauto
       usage in apply step_fst, see hypothesis *)
    Local Hint Resolve to_of_val : core.

    Lemma bin_log_rel_fst Γ t1 t2 p1 p2 : 
        Γ ⊨ p1 ≤log≤ p2 : TProd t1 t2 -∗
        Γ ⊨ Fst p1 ≤log≤ Fst p2 : t1.
    Proof.
        (* assumptions *)
        iIntros "#Hp" (rho ws) "!#(#Hs & #Hgam)" .
        iIntros (K) "Hspec". 
        (* specialize Hp *)
        iSpecialize ("Hp" $! rho ws with "[# $Hs $Hgam]").
        (* use bind to get to fill FstCtx e*)
        iApply (interp_expr_bind' [FstCtx] [FstCtx]).
        { iApply "Hp". }
        2:{ asimpl. iApply "Hspec". }
        (* the main proof of the expr bind *)
        iIntros ([v  v']) "#Hv".
        (* break apart the hypothesis intepr (v ,v') *) 
        iDestruct "Hv" as ([v1 v1'][v2 v2']) "#[%Heq [Hv1 Hv2]]" ;fold interp in * 
        ;simpl in Heq; inversion Heq; subst; simpl. 
        (* we have Fst (Pair _ _ ) which can step*)
        (* first, take in the spec config *)
        iIntros (K') "Hspec "; simpl.
        (* now step *)
        iApply wp_pure_step_later; try done.
        iIntros "!> _".
        (* take a specification step *)
        iMod (step_fst with "[Hspec]") as "Hspec'" ; eauto .
        iApply wp_value.
        iExists v1'.
        iSplit.
        - iApply "Hspec'".
        - iApply "Hv1".
    Qed.

    Lemma bin_log_rel_snd Γ t1 t2 p1 p2 : 
        Γ ⊨ p1 ≤log≤ p2 : TProd t1 t2 -∗
        Γ ⊨ Snd p1 ≤log≤ Snd p2 : t2.
    Proof.
        (* assumptions *)
        iIntros "#Hp" (rho ws) "!#(#Hs & #Hgam)" .
        iIntros (K) "Hspec". 
        (* specialize Hp *)
        iSpecialize ("Hp" $! rho ws with "[# $Hs $Hgam]").
        (* use bind to get to fill SndCtx e*)
        iApply (interp_expr_bind' [SndCtx] [SndCtx]).
        { iApply "Hp". }
        2:{ asimpl. iApply "Hspec". }
        (* the main proof of the expr bind *)
        iIntros ([v  v']) "#Hv".
        (* break apart the hypothesis intepr (v ,v') *) 
        iDestruct "Hv" as ([v1 v1'][v2 v2']) "#[%Heq [Hv1 Hv2]]" ;fold interp in * 
        ;simpl in Heq; inversion Heq; subst; simpl. 
        (* we have Snd (Pair _ _ ) which can step*)
        (* first, take in the spec config *)
        iIntros (K') "Hspec "; simpl.
        (* now step *)
        iApply wp_pure_step_later; try done.
        iIntros "!> _".
        (* take a specification step *)
        Check step_snd.
        iMod (step_snd with "[Hspec]") as "Hspec'" ; eauto .
        iApply wp_value.
        iExists v2'.
        iSplit.
        - iApply "Hspec'".
        - iApply "Hv2".
    Qed.

    Lemma bin_log_rel_osum Γ t c1 c2 e1 e2 : 
        Γ ⊨ c1 ≤log≤ c2 : TCase t -∗
        Γ ⊨ e1 ≤log≤ e2 : t -∗
        Γ ⊨ Inj c1 e1 ≤log≤ Inj c2 e2 : TOSum.
    Proof.
        (* assumptions *)
        iIntros "#Hc #He" (rho ws) "!#(#Hs & #Hgam)" .
        iIntros (K) "Hspec". 
        (* specialize  *)
        iSpecialize ("Hc" $! rho ws with "[# $Hs $Hgam]").
        iSpecialize ("He" $! rho ws with "[# $Hs $Hgam]").
        (* bind *)
        iApply (interp_expr_bind' [InjLCtx _] [InjLCtx _]).
        { iApply "Hc". }
        2:{ iApply "Hspec". }
        iIntros ([cv1 cv2]) "#Hcv".
        iApply (interp_expr_bind' [InjRCtx _] [InjRCtx _]).
        {iApply "He". }
        iIntros ([ev1 ev2]) "#Hev".
        (* open the invariant *)
        iIntros (K') "Hj /=".
        iDestruct "Hcv" as "[%l [%l' [%Heqcase Hinv]]]"; fold interp in *; inversion Heqcase; subst.

        (* So we can open the invariant *)
        iApply fupd_wp.
        (* performing a lookup..? *)
        iInv (logN .@ (l,l')) as "[%l'' [#>d [#>e #f]]]".
        
        (* show the invariant still holds, it does because we didnt
         modify it *)
        iModIntro.
        simpl.
        iSplit.
        - iNext. unfold case_inv. unfold pointsto_def. simpl.
        iExists l''. repeat iSplit ; try done.
        -
        (* now prove the Wp *)
        iModIntro.
        iApply wp_value.
        iExists (InjV (CaseV l') ev2).
        iSplit.
        iApply "Hj".
        iExists l , l' , ev1 ,ev2 ,(interp t rho).
        repeat iSplit; try done.
        iNext.
        iExists l''.
        repeat iSplit; try done.
    Qed.

    Lemma bin_log_rel_caseof Γ e1 e2 e3 e4 e1' e2' e3' e4' t1 t2: 
        Γ ⊨ e1 ≤log≤ e1' : TOSum -∗
        Γ ⊨ e2 ≤log≤ e2' : TCase t1 -∗
        t1 :: Γ ⊨ e3 ≤log≤ e3' : t2 -∗
        Γ ⊨ e4 ≤log≤ e4' : t2 -∗
        Γ ⊨ CaseOf e1 e2 e3 e4 ≤log≤ CaseOf e1' e2' e3' e4' : t2.
    Proof.
        (* assumptions *)
        iIntros "#Ho #Hc #Htru #Hfls" (rho ws) "!#(#Hs & #Hgam)" .
        iIntros (K) "Hspec". 
        (* specialize  *)
        iSpecialize ("Ho" $! rho ws with "[# $Hs $Hgam]").
        iSpecialize ("Hc" $! rho ws with "[# $Hs $Hgam]").
        iSpecialize ("Hfls" $! rho ws with "[# $Hs $Hgam]").
        (* reduce *)
        iApply (interp_expr_bind' [CaseOfCtxOSUM _ _ _] [CaseOfCtxOSUM _ _ _]).
        { iApply "Ho". }
        2:{ iApply "Hspec". } 
        iIntros ([ov1 ov2]) "#Hov".
        iApply (interp_expr_bind' [CaseOfCtxInj _ _ _] [CaseOfCtxInj _ _ _]).
        { iApply "Hc". } 
        iIntros ([cv1 cv2]) "#Hcv".
        (* use the value relation data for osum *)
        iDestruct "Hov" as "[%l1 [%l1' [%ov1' [%ov2' [%R [%Heq [[%l3 [>nbij1 [>rbij1 pred1]]] Rel]]]]]]]".
        inversion Heq. subst. 
        (* use the value relation data for case *)
        iDestruct "Hcv" as "[%l2 [%l2' [%Hceq Cinv]]]". fold interp in *.
        inversion Hceq. subst.
        (* destruct the case invariant *)
  (*       iDestruct "Cinv" as "[#l2in [#l2'in [%l3' [nbij2 [rbij2 pred2]]]]]". *)
(*         iDestruct "Cinv" as "[%l3' [nbij2 [rbij2 pred2]]]". 
 *)    
        iIntros (K') "Hspec'".
        iApply fupd_wp.
        iInv (logN.@(l2, l2')) as "[%l3' [>#nbij2 [>#rbij2 #pred2]]]".
        (* prove invariant still holds. *)
        iModIntro.
        iSplit.
        {iExists l3'. repeat iSplit ; try done. }
        iModIntro.


        destruct (decide (l1 = l2)) as [|Hneq]. subst.
        {
            iPoseProof (gset_bij_own_elem_agree with "nbij1 nbij2") as "%foo".
            destruct foo.
            pose proof (H1 (eq_refl l2)). subst.
            iPoseProof (gset_bij_own_elem_agree with "rbij1 rbij2") as "%bar".
            destruct bar.
            pose proof (H3 (eq_refl _)). subst.
            iPoseProof (@saved_pred_agree _ _ _ _ _ _  _ _ (ov1' , ov2') with "pred1 pred2") as "baz".
            iMod (step_caseOf_true with "[Hspec']") as "yosh".
            3:{
                iSplit. - iApply "Hs". -iApply "Hspec'".
            }
            {
                apply to_of_val.
            }
            { eauto. }
            
            iApply wp_pure_step_later; try done.
            iNext. 
            iIntros "lc".
            asimpl.
            iSpecialize ("Htru" $! rho ((ov1' , ov2') :: ws)).

            iAssert (▷ ⟦ t1 :: Γ ⟧* rho ((ov1', ov2') :: ws))%I  as "Hext".
            - iApply interp_env_cons.
            iSplit.
            + iNext. iRewrite -"baz". iApply "Rel".
            + iApply "Hgam".
            -
            (* Use the later credit *)
            iAssert (£ 1 -∗ ▷ ⟦ t1 :: Γ ⟧* rho ((ov1', ov2') :: ws) ={⊤}=∗ ⟦ t1 :: Γ ⟧* rho ((ov1', ov2') :: ws))%I as "credit".
            { iApply lc_fupd_elim_later. } 
            iPoseProof ("credit" with "lc Hext") as ">yes". 

            iSpecialize ("Htru"  with "[Hs yes]").
            + iSplit. iApply "Hs". done. 
            + asimpl.
            iApply "Htru". simpl.
            iApply "yosh".
        }
        iPoseProof (gset_bij_own_elem_agree with "nbij1 nbij2") as "%foo".
        assert (l1' <> l2').
        {
            destruct foo. unfold not. intros. auto.
        }
        iMod (step_caseOf_false with "[Hspec']") as "yosh".
        4: {
            iSplit. - done.
            - iApply "Hspec'".
        }
        { apply to_of_val. } done. done.
        iApply wp_pure_step_later.
        { apply wp_case_nomatch. - red. exists ov1'. done. - done. }
        done.
        iIntros "!> _".
        iApply "Hfls".
        iApply "yosh".
    Qed.

    Lemma views (e : expr)(s s' : gsetUR loc)(p : s ⊆ s') :
        own config_name (● (Excl' e , s') ⋅ ◯ (Excl' e , s')) ==∗ 
        own config_name (● (Excl' e , s')) ∗
        own config_name (◯ (None , s)) ∗
        own config_name (◯ (Excl' e , empty)) .
    Proof.
        iIntros "[Hauth Hview]".
        (* create the view for the expression *)
        assert (● (Excl' e , s') ~~> ● (Excl' e , s') ⋅ ◯ (None, s')). {
            apply auth_update_alloc.
            apply prod_local_update_2.
            apply gset_local_update. done.
        }

        assert (◯ (None, s') ~~> ◯ (None : spec_thread, s)). {
            apply view_update_frag.
            intros.
            destruct H2.
            split.
            2 :{ done. }
            eapply cmra_includedN_trans.
            2 :{ exact H2. }
            apply cmra_monoN_r.
            apply prod_includedN; simpl.
            split. try done.
            set_solver.
        }
        (* create the view for the state *)
        assert (◯ (Excl' e , s') ~~> ◯ (Excl' e, empty)). {
            apply view_update_frag.
            intros.
            destruct H3.
            split.
            2:{ done. }
            eapply cmra_includedN_trans.
            2:{ exact H3. }
            apply cmra_monoN_r.
            apply prod_includedN. simpl.
            split . done.
            set_solver.
        }
        iPoseProof (own_update config_name _ _ H1 with "Hauth") as ">[Hauth Hview1]".
        iPoseProof (own_update config_name _ _ H3 with "Hview") as ">Hview2".
        iPoseProof (own_update config_name _ _ H2 with "Hview1") as ">Hview1".
        iModIntro.
        iSplitL "Hauth" ; try done.
        iSplitL "Hview1"; done.
    Qed.



    Lemma bin_log_rel_new Γ t : 
        ⊢ Γ ⊨ New t ≤log≤ New t : TCase t.
    Proof.
        iIntros (rho ws) "!#(#Hs & #Hgam)".
        iIntros (K) "Hspec". 
        (* step 1: take a step in the implementation *)
        iApply wp_lift_atomic_base_step_no_fork.
        { done. }
        iIntros (s n1 k1 k2 n2) "ownS". 
        iModIntro. iSplit.
        { iPureIntro; unfold base_reducible; repeat eexists; eapply NewS. }
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        inversion baseStep; subst; iSplitR ; try done; simpl in *; clear.
        (* Goal at this point is
            - 2: take a specification step
            - 3: update the specification invariant
            - 4: update the logical state
            - 5: show state interpretation invariant still holds
            - 6: prove the WP condition, relational interpretation of Case
        *)

        (* Step 2: take a specification step *)
        (* break open all the data in the state interpretation and the spec_ctx invariant *)
        iDestruct "ownS" as "[%s' [%s'' [cfg  [nbij [rbij preds]]]]]".
        iDestruct "Hs" as "[%ei [%si inv]]".
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]".

        (* 
            From the spec invariant, we know
                own config_name (● (Excl' ei', list_to_set si'))

            From the state interpretation, we know
                own config_name (◯ (None, list_to_set s'))

            From the definition of expression relation, we know
                ⤇ fill K (New t) 
                or
                own config_name (◯ (Excl' (fill K (New t)), empty)

            combine all this information 
         *)
        iCombine "Hspec" "cfg" as "cfgv".
        iCombine "Hown cfgv" gives
        %[[Htpj Hslt]%prod_included _]
            %auth_both_valid_discrete.
        simpl in *.
        (*  *)
        assert (Excl' (fill K (New t)) ⋅ None = (Excl' (fill K (New t)) : spec_thread)) as eqexpr by done.
        rewrite eqexpr.
        rewrite eqexpr in Htpj.
        clear eqexpr.
        apply Excl_included in Htpj.
        assert (ei' = fill K (New t)) by done; subst.
        (* 
            Now we have
                own config_name (● (Excl' (fill K (New t)), list_to_set si'))
                own config_name (◯ (Excl' (fill K (New t)), list_to_set s'))
                list_to_set s' ≼ list_to_set si'

            importantly, "ei'", the expression held by the spec is equal to "fill K (New t)"
            and 
            "s' ≼ si'" 
                where "s'" := the state held by the state interpretation 
                      "si'":= the state held by the spec 


            Now that we know the authoritative element of the spec config,
            we can take an execution step.
        *)

        assert (rtc (@erased_step OSum_lang) ([ei],si)([fill K (Case (fresh si'))], (fresh si') :: si')) as Hrtc'.
        {
            eapply rtc_r. exact Hrtc.
            exists [].
            apply (@step_atomic OSum_lang _ [] _  (fill K (New t)) si' (fill K (Case (fresh si')))(fresh si' :: si')[] [] []); try done.
            econstructor; try done.
            apply (NewS t si').
        }
        (* 
            Now we need to update the authoritative element of the specification configuration
            to reflect the fact that we have steped from 
            (New t, si') to (Case (fresh si'), (fresh si') + si') *)
        iMod (own_update_2 with "Hown cfgv") as "Hspec'".
        {
            apply auth_update with 
                (a' := (Excl' (fill K (Case (fresh si'))) : spec_thread, list_to_set (fresh si' :: si')))
                (b' := (Excl' (fill K (Case (fresh si'))) : spec_thread, list_to_set (fresh si' :: si'))).
            apply prod_local_update'; simpl.
            apply option_local_update.
            eapply exclusive_local_update ; try done.
            apply gset_local_update. set_solver.
        }

        (* We need to allocate a few views of the authoritative element to
        satisfy the goals below *)
        iPoseProof (views _ (list_to_set (fresh si' :: s')) (list_to_set (fresh si' :: si')) with "Hspec'") as ">[Hauth [Hviewstate Hviewexpr]]".
        { set_solver. }

        (* Step 3 : restablish the specification invariant *)
        iModIntro.
        iSplitL "Hauth".
        {
            iModIntro.
            (* Choose our new reachable configuration *)
            iExists (fill K (Case (fresh si'))) , (fresh si' :: si').
            iSplit.
            - (* Show the updated resources *)
            iApply "Hauth".
            - (* and that this new config is reachable *)
            iPureIntro.
            exact Hrtc'.
        }
        clear - Hslt.

        (* Step 4: update the logical state *)
        unfold binary_logrel.state_interp.

        (* update the name bijection *)
        assert (forall b', (fresh s, b') ∉ (binary_logrel.combine s s')) as c1. {
            intros.
            eapply not_in_combine_left.
            apply infinite_is_fresh.
        }
        (* critical here is the assumption 
            list_to_set s' ≼ list_to_set si'
        *)
        assert (fresh si' ∉ s') as sfresh. {
            pose proof (infinite_is_fresh si').
            set_solver.
        }
        assert (forall a', (a', fresh si') ∉ (binary_logrel.combine s s')) as c2.
        {
            intros.
            apply not_in_combine_right.
            apply sfresh. 
        }

        iPoseProof (gset_bij_own_extend (fresh s) (fresh si') c1 c2 with "nbij" ) as ">(nbijauth & nbijview)".
        pose proof (adjust_combine (fresh s) (fresh si') (infinite_is_fresh s) (sfresh)) as nbijadjust.
        (* allocate a new predicate  *)
        iMod (saved_pred_alloc_cofinite (list_to_set s'') (interp t rho) DfracDiscarded ) as "[%lp [%lpnotin #npred]]"; try done.
        assert (lp ∉ s'') as lpfresh. { rewrite elem_of_list_to_set in lpnotin. done. }
       
        (* update the predicate bijection *)
        assert ((fresh s , fresh si') ∉ zip s s') as pairfresh . {
            unfold not.
            intros Hyp.
            apply elem_of_zip_l in Hyp.
            pose proof (infinite_is_fresh s).
            contradiction.
        }
        assert (forall b', ((fresh s, fresh si'), b') ∉ (binary_logrel.combine (zip s s') s'')) as c3. {
            intros.
            apply not_in_combine_left.
            apply pairfresh.
        }
        assert (forall a', (a' , lp) ∉  (binary_logrel.combine (zip s s') s'')) as c4. {
            intros.
            apply not_in_combine_right.
            done.
        }
        iPoseProof (gset_bij_own_extend (fresh s , fresh si') lp c3 c4 with "rbij" ) as ">(rbijauth & rbijview)".
        pose proof (adjust_combine (fresh s , fresh si') lp pairfresh lpfresh) as rbijadjust.

        (* step 5: show state interpretation invariant still holds *)
 
        iSplitL "Hviewstate nbijauth rbijauth preds npred".
        {
            iModIntro.
            iExists (fresh si' :: s'), (lp :: s'').
            iSplit. iApply "Hviewstate".  
            iSplitL "nbijauth".
            { rewrite -nbijadjust. done. }
            iSplitL "rbijauth".
            { rewrite -rbijadjust. done. }
            rewrite big_opL_cons.
            iSplit.
            - iExists (interp t rho); iApply "npred".
            - iApply "preds".
        }

        (* step 6: prove the WP condition, relational interpretation of Case *)
        clear.
        iExists (CaseV (fresh si')).
        iSplitL "Hviewexpr". { iModIntro. iApply "Hviewexpr". }
        iExists (fresh s) , (fresh si').
        iSplitR; try done.
        iApply (inv_alloc).
        iModIntro.
        iExists lp.
        repeat try iSplit ; try done.
    Qed.


    Theorem binary_fundamental Γ e t : 
        Γ ⊢ₜ e : t → ⊢ Γ ⊨ e ≤log≤ e : t.
    Proof.
        intros typ.
        induction typ.
        - admit.
        - iApply bin_log_rel_unit.
        - iApply bin_log_rel_int.
        - iApply bin_log_rel_bool.
        - admit.
        - admit.
        - iApply bin_log_rel_pair ; done.
        - iApply bin_log_rel_fst; done.
        - iApply bin_log_rel_snd; done.
        - iApply bin_log_rel_osum ; done.
        - iApply bin_log_rel_caseof; done.
        - iApply bin_log_rel_new. 
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
    Admitted.
End fundamental.