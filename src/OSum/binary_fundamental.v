From stdpp Require Import base gmap coPset tactics proof_irrel sets.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
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
        (* we have values *)
        iApply (interp_expr_val (InjV _ _, InjV _ _)).
        (* break apart our assumptions on the pair or cases and pair of e:t  *)
        iDestruct "Hcv" as "[%l [%l' [%Heqcase Hinv]]]"; fold interp in *; inversion Heqcase; subst.
(*         iDestruct "Hinv" as "[limp [lspec point]]".
 *)     unfold case_inv in *.   
        iExists l , l' , ev1 , ev2, (interp t rho).
        repeat iSplit ; try done.
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
        iDestruct "Hov" as "[%l1 [%l1' [%ov1' [%ov2' [%R [%Heq [[%l3 [nbij1 [rbij1 pred1]]] Rel]]]]]]]".
        inversion Heq. subst. 
        (* use the value relation data for case *)
        iDestruct "Hcv" as "[%l2 [%l2' [%Hceq Cinv]]]". fold interp in *.
        inversion Hceq. subst.
        (* destruct the case invariant *)
  (*       iDestruct "Cinv" as "[#l2in [#l2'in [%l3' [nbij2 [rbij2 pred2]]]]]". *)
        iDestruct "Cinv" as "[%l3' [nbij2 [rbij2 pred2]]]". 
    
        iIntros (K') "Hspec'".
        simpl.

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
            iIntros "!> _".
            asimpl.
            iSpecialize ("Htru" $! rho ((ov1' , ov2') :: ws)).
            iAssert (⟦ t1 :: Γ ⟧* rho ((ov1', ov2') :: ws))%I as "Hext".
            - iApply interp_env_cons.
            iSplit.
            + iRewrite -"baz". iApply "Rel".
            + iApply "Hgam".
            - iSpecialize ("Htru"  with "[Hs Hext]").
            + iSplit. iApply "Hs". iApply "Hext".
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

    Check New.
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
        iIntros (s1 _ k1  _ _) "ownS". 
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


        unfold case_inv. unfold pointsto_def. simpl.

        iApply wp_lift_atomic_base_step_no_fork; auto; simpl.
        iIntros (s _ k1  _ _) "ownS". 
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

        iSplitR ; try done.
        iMod (do_step_new with "[Hspec]") as "[%sspec Hspec]".
        { done. }
        { iSplit; done. }
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
    Admitted.


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