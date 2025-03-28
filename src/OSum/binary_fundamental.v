From stdpp Require Import base gmap coPset tactics proof_irrel sets.

From iris.base_logic Require Import base_logic invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map gset_bij.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
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

    Check interp_expr.
    Check interp.
    Check interp_env.
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


(*         (* break apart out assumptions on the pair or cases and pair of e:t  *)
        iDestruct "Hcv" as "[%l [%l' [%Heqcase Hinv]]]"; fold interp in * ;inversion Heqcase; subst.
        iIntros (K') "Hspec".
        iInv "Hinv" as "foo". (* if we use inv, can use iInv when the goal is a Wp *)
        {
            apply ectx_language_atomic; simpl.
            2:{ red. intros. inversion H1. }
            simpl. red. intros. apply prim_base_irreducible.
             red. intros. unfold not. intros.  
        }
 *)

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

    (*  In the unary version.. I have the authoritative element of the 
    bijection given from the state interpretation.. 
    
    Which .. seems fine in the unary case
    but in the binary case, the state interpretation including the 
    authoritative element of the bijection is positing
    the existence of a separate executeion whos program state is 
    in bijection with the currently running program..

    Maybe this is a misuse of the state interpretation and it should
    instead be an invariant on the locations
    *)
    Lemma wp_new t  : 
        ⊢ WP (New t) {{ v, ∃ l (s s' : list loc), ⌜v = CaseV l⌝ ∗ gset_bij_own_elem name_bij (fresh s) (fresh s') }}.
    Proof.
        Check inv_alloc.
        iApply wp_lift_atomic_base_step_no_fork; auto;  simpl.
        iIntros (s1 _ k1  _ _) "[%es [%s' ownS]]". 
                    (* get access to the state interpretation *)
        unfold binary_logrel.state_interp; simpl; unfold state_interp.
        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* only obligation is that we need to be able to summon a fresh name *)
    (*         exact (is_fresh s1).
    *)      - (* now we need to handle the state update, 
            first bring variables into scope  *)
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep. subst. 
        
(*         simpl. 
        iApply fupd_frame_l.
        iSplit; try done.
        iApply fupd_frame_r. *)
    Admitted.
 (*        iSplit.
        2:{ iExists (fresh s1). done. }
        iMod (own_update with "[ownS]") as "goal".
        2:{ iApply "ownS". }
        { 
            red.
        } 
        Check auth_update.
        iApply own_update.
        Check own_update. *)

    
    Lemma bin_log_rel_new Γ t : 
        ⊢ Γ ⊨ New t ≤log≤ New t : TCase t.
    Proof.
        iIntros (rho ws) "!#(#Hs & #Hgam)".
        iIntros (K) "Hspec". 
       
(*         iDestruct "Hs" as (ei si) "Hs".
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]"; simpl.

        iApply wp_wand.
        iApply wp_new.
        iIntros.
        simpl.
        simpl.
        iMod (do_step_new with "[Hspec]") as "[%sspec Hspec]".
        { done. }
        { iSplit; done. }
        iDestruct "Hs" as (ei si) "Hs".
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]".
 *)


(*         simpl. unfold case_inv. unfold pointsto_def. simpl.
 *)
        iApply wp_lift_atomic_base_step_no_fork.
        { done. } (* auto; simpl. *)
        iIntros (s n1 k1 k2 n2) "ownS". 
                    (* get access to the state interpretation *)
(*         unfold binary_logrel.state_interp; simpl; unfold state_interp.
 *)        (* handle the fact that New is reducible first *)
        iModIntro. iSplit.
        - iPureIntro; unfold base_reducible; repeat eexists; eapply NewS.
        (* only obligation is that we need to be able to summon a fresh name *)
    (*         exact (is_fresh s1).
    *)      - (* now we need to handle the state update, 
            first bring variables into scope  *)
        iModIntro. iIntros (e2 s2 efs baseStep) "lc".
        (* inversion on the base step *)
        inversion baseStep. subst.

        iSplitR ; try done.
        Search from_option. simpl in *.

        (*  *)
        iDestruct "ownS" as "[%s' [%s'' [cfg  [nbij [rbij preds]]]]]".
        iDestruct "Hs" as "[%ei [%si inv]]".
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]".

         iCombine "Hspec" "cfg" as "cfgv".
 (*         iCombine "Hown" "cfgv" as "new".
 *)      iCombine "Hown cfgv" gives
        %[[Htpj huh]%prod_included ?]
            %auth_both_valid_discrete.
        simpl in *.
        (*  *)
        Check {[0 := Excl (fill K (New t))]}.
        assert ({[0 := Excl (fill K (New t))]} ⋅ ∅ = ({[0 := Excl (fill K (New t))]} : spec_thread)).
        {
            set_solver.
        }
        rewrite H2.
        rewrite H2 in Htpj.
        apply singleton_included_l in Htpj as [e'' [f g]].
        Check lookup_singleton.
        rewrite lookup_singleton in f.
        rewrite -f in g.
        apply Excl_included in g. symmetry in g.
        assert (ei' = fill K (New t)) by done; subst.
        (* perform a step in the spec *)
        assert (rtc (@erased_step OSum_lang) ([ei],si)([fill K (Case (fresh si'))], (fresh si') :: si')) as Hrtc'.
        {
            eapply rtc_r. exact Hrtc.
            exists [].
            apply (@step_atomic OSum_lang _ [] _  (fill K (New t)) si' (fill K (Case (fresh si')))(fresh si' :: si')[] [] []); try done.
            econstructor; try done.
            apply (NewS t si').
        }
        (* Now we need to update the authoritative element of the configuration
        to reflect our new choice of e' and s' *)

        iMod (own_update_2 with "Hown cfgv") as "[Hauth _]".
        {
            apply (auth_update _ _ 
                (<[0 := Excl (fill K (Case (fresh si')))]> {[0 := Excl (fill K (New t))]}, list_to_set (fresh si' :: si'))
                ({[0 := Excl (fill K (Case (fresh si')))]}, list_to_set (fresh si' :: si'))) .
            apply prod_local_update' ; simpl.
            (* first update the program expression  *)
        {
                eapply singleton_local_update.
                {
                    rewrite lookup_singleton. done.
                }
                eapply exclusive_local_update. done.
            }
            (* now update the program state *)
    (*         apply gset_disj_alloc_op_local_update.
            eapply gset_local_update. *)
            unfold local_update. simpl.
            intros.
            split; try done.
            rewrite H4. 
            destruct mz ; simpl ; set_solver.
        }
        assert ({[0 := Excl (fill K (Case (fresh si'))); 0 := Excl (fill K (New t))]} = ({[0 := Excl (fill K (Case (fresh si')))]} : spec_thread)).
        {
            set_solver.
        }
        rewrite H3.
        clear H3.
        (* create the view for the state interpretation *)
        set cfg := ({[0 := Excl (fill K (Case (fresh si')))]}, list_to_set (fresh si' :: si')).
        Check (auth_update_alloc cfg cfg (empty, list_to_set (fresh si' :: si'))).
        assert (● cfg ~~> ● cfg ⋅ ◯ (empty, list_to_set (fresh si' :: s'))). {
            apply auth_update_alloc.
            apply prod_local_update'; simpl.
            2:{
                unfold local_update.
                intros. simpl in *.
                split.
                done.
                destruct mz.
                {
                    assert (c = {[fresh si']} ∪ list_to_set si').
                    set_solver.
                    subst.
                    set_solver.
                }
                exfalso.
                set_solver.
                (* apply gset_local_update. set_solver. *)
            }
            apply gmap_local_update.
            intros.
            destruct (decide (0 = i)) .
            { 
                subst.
                rewrite lookup_singleton.
                done.
(*                 eapply exclusive_local_update. done.
 *)            }
            pose proof (lookup_singleton_ne 0 i (Excl (fill K (Case (fresh si')))) n).
            rewrite H3. done. 
        }
        iPoseProof (own_update config_name _ _ H3 with "Hauth") as ">Hauth".
        iPoseProof (own_op config_name _ _ with "Hauth") as "[Hauth Hviewstate]".

        (* create the view for the WP post condition *)
        assert (● cfg ~~> ● cfg ⋅ ◯ ({[0 := Excl (fill K (Case (fresh si')))]}, empty)). {
            apply auth_update_alloc.
            apply prod_local_update'; simpl.
        {
            apply gmap_local_update.
            intros.
            destruct (decide (0 = i)).
            {
                subst.
                rewrite lookup_singleton.
                unfold local_update.
                intros. simpl in *.
                split.
                done.
                rewrite lookup_empty in H5.
                destruct mz.
                {
                    simpl in H5.
                    destruct c.
                    {
                        
                    }
                }
                simpl in H5.
                unfold opM in H5.
                repeat red in H5. 
                set exp := Excl' (fill K (Case (fresh si'))).
                destruct mz.
                {
                    simpl.
                    destruct c.
                    {
                        rewrite 
                    simpl in H5.
                       compute.   
                    }
                }
                destruct (mz = Some (Some (excl'  exp))).
(*                 eapply exclusive_local_update. done.
 *)            }
            pose proof (lookup_singleton_ne 0 i (Excl (fill K (Case (fresh si')))) n).
            rewrite H4.
            done.
        }
        done.
        }

        iPoseProof (own_update config_name _ _ H4 with "Hauth") as ">Hauth".
        iPoseProof (own_op config_name _ _ with "Hauth") as "[Hauth Hviewexpr]".


        (* Now we can reestablish the spec invariant *)
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
        unfold binary_logrel.state_interp.
        Check gset_bij_own_extend.

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
            (* clear huh. see, removin the hypothesis is bad *)
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
        Check saved_pred_alloc_cofinite.
        iMod (saved_pred_alloc_cofinite (list_to_set s'') (interp t rho) DfracDiscarded ) as "[%lp [%lpnotin #npred]]"; try done.
        assert (lp ∉ s'') as lpfresh. { rewrite elem_of_list_to_set in lpnotin. done. }
        (* update the predicate bijection *)
        Check not_in_combine_left.
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

        (* all the data is there, now time to dispatch the state interpretation *)
        Check inv_alloc.
(*         iMod (inv_alloc (logN.@(l, l')))
 *)        Check fupd_frame_l ⊤ ⊤ .

        Check fupd_frame_l.
        Check inv_alloc.

        iSplitL "Hviewstate nbijauth rbijauth preds npred".
        {
            iModIntro.
            iExists (fresh si' :: s'), (lp :: s'').
            iSplit. done.
            iSplitL "nbijauth".
            { rewrite -nbijadjust. done. }
            iSplitL "rbijauth".
            { rewrite -rbijadjust. done. }
            rewrite big_opL_cons.
            iSplit.
            - iExists (interp t rho); done.
            - done.
        }

        (* now to prove the Wp post condition *)
        iExists (CaseV (fresh si')).

        unfold case_inv.
        unfold pointsto_def.
        simpl.
        iSplitL "Hviewexpr"; try done.
 
        iExists (fresh s) , (fresh si').
        clear.
        iSplitR; try done.
        iApply (inv_alloc).
        iModIntro.
        iExists lp.
        repeat try iSplit ; try done.

        Unshelve.
        unfold Exclusive.
        intros.
        Check lookup_empty.
        rewrite lookup_empty in H4.
        destruct y.
        + compute in H4. admit.
        + compute in H4.
        Check option_valid.

         

        (* goal, can i use 
          Lemma auth_frag_included dq a b1 b2 :
            ◯ b1 ≼ ●{dq} a ⋅ ◯ b2 ↔ b1 ≼ b2. 
        
            to 
        *)


(* 
        (* open the state invariant data *)
        iDestruct "ownS" as "[%e [%s' [%s'' [cfg  [nbij [rbij preds]]]]]]".
        iCombine "Hspec" "cfg" as "cfgv".

        (* wait... by threading ownership of config through the state interp...
        
        are we in conflict with the "spec_ctx" that holds an authoritative element of the config?

        perhaps not. since the element is exclusive, so we just have two 


        having two auth elements at the same gname feels incorrect...
        one of them has to be used to reestablish the invariant

        Having ownership with DFrac 1 twice can be used to derive False

        Does unfolding the "do_step_new" proof here help at all..?
        *)
 *)


        
        iMod (do_step_new with "[Hspec]") as "[%sspec Hspec]".
        { done. }
        { iSplit; done. }
        simpl.
        iDestruct "ownS" as "[%e [%s' [%s'' [cfg  [nbij [rbij preds]]]]]]".
        (* combine the config data  *)
        iCombine "cfg" "Hspec" gives "%cfg".
        rewrite auth_frag_op_valid in cfg.
        Check cmra_valid_op_r _ _ cfg.
        Check pair_op.
        rewrite -pair_op in cfg.
        Check cmra_valid_op_r.
        rewrite pair_valid  in cfg.
        destruct cfg as [ev sv].
        compute in sv.

        unfold op in sv.

        pose proof (cmra_valid_op_r cfg).
        Check valid_op.
        rewrite prod_validI in cfg.
        Check prod_valid.
        apply auth_frag_valid in cfg.
        Check auth_frag_op_valid.


        apply auth_both_valid_discrete in cfg as [inc _].
        apply prod_included in inc as [tp st]. simpl in *.
        apply singleton_included_l in tp as [exc [lkup einc]].
        rewrite lookup_singleton in lkup.
        rewrite -lkup in einc.
        apply Excl_included in einc.
        apply gset_included in st.
        

        

        apply auth_both_dfrac_valid in huh as [huh1 [huh2 huh3]].


    Admitted.
(*         
        iDestruct "ownS" as "[%s' [%s'' [d e]]]". simpl.
        iSplitR "Hspec".
        2:{
            iModIntro.
            iExists (CaseV (fresh sspec)). simpl.
            iSplit.
            + admit.
            + iExists (fresh s), (fresh sspec).
            iSplit; try done.
            unfold case_inv.
            unfold pointsto_def. simpl.
            admit.
         }
        iModIntro.
        iExists (fresh s' :: s) ,s''.
        iSplitL.
        +
        iExists ((fresh sspec) :: sspec) , s'.
        iSplitL.
        * iApply auth_own_mono.


        iCombine "Hspec" "d" gives "%what".
        simpl in what.


        iModIntro.
        iSplitL.
        iExists ((fresh sspec) :: sspec).
        iSplit.
        iApply fupd_frame_l.
        iSplitL.
        + iIntros (s') "Hbij".

   
        simpl.


        asimpl.
        iApply wp_wand.
        iApply wp_new.
        iIntros (v) "[%l [%leq ownl]]". subst.
        

        unfold case_inv. unfold pointsto_def. simpl. subst.
    Admitted. *)


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