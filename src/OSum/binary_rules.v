From stdpp Require Import base gmap.

From iris.base_logic Require Import invariants iprop upred saved_prop.
From iris.base_logic.lib Require Import gset_bij .
From iris.algebra Require Import gset_bij excl gmap gset cmra.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.


From MyProject.src.OSum Require Export OSum persistent_pred wp_rules.

Class testRes Σ := {
    sets :: inG Σ (authR (gsetUR loc));
    name : gname
}.
(* Section test.
    Context `{testRes Σ}.

    (* no.. if the authoritative element was in scope.. you might be able to show this
    with two usages of 
        Lemma view_frag_included p a b1 b2 :
            ◯V b1 ≼ ●V{p} a ⋅ ◯V b2 ↔ b1 ≼ b2.
    *)
    Example ex s s' : own name (◯ s) ∗ own name (◯ s') -∗ ⌜s = s'⌝.
    Proof.
        iIntros "[os os']".
        iCombine "os os'" as "foo". simpl.

 *)
Definition specN := nroot .@ "spec".

Definition D `{Σ : gFunctors}:= persistent_pred (val * val) (iProp Σ).

Definition spec_thread : ucmra := gmapUR nat (exclR exprO).

Definition configRA : cmra := prodUR spec_thread (gsetUR loc).

Class configSpec Σ := CS { 
    config_in :: inG Σ (authR configRA) ; 
(*     spec_predicates :: savedPredG Σ (val * val) ;
 *)    config_name : gname
}.

Check authR.
Section definitionsS.
    Context `{configSpec Σ, invGS Σ}.

    Definition spec_inv (e : expr)(s : state) : iProp Σ := 
        (∃ e' s', own config_name (● ({[ 0 := Excl e']} , (list_to_set s')))
                    ∗ ⌜rtc erased_step ([e],s) ([e'],s')⌝)%I.

    Definition spec_ctx : iProp Σ :=
        (∃ e s, inv specN (spec_inv e s))%I.

    Definition tpool_pointsto (e : expr) : iProp Σ :=
        own config_name (◯ ({[ 0 := Excl e ]}, ∅)).
    
    Definition spec_state_elem (l : loc) : iProp Σ :=
        own config_name (◯ (empty, {[ l ]})).

    Global Instance spec_ctx_persistent : Persistent spec_ctx.
    Proof. apply _. Qed.

End definitionsS.

Notation "⤇ e" := (tpool_pointsto e) (at level 20) : bi_scope.
Notation "l ∈s" := (spec_state_elem  l) (at level 20) : bi_scope.


Section cfg.
    Context `{ invGS Σ , configSpec Σ}.

    Lemma step_pure' E  K e e' (P : Prop) n :
        P →
        PureExec P n e e' →
        nclose specN ⊆ E →
        spec_ctx ∗ (⤇ fill K e) ={E}=∗ (⤇ fill K e').
    Proof.
        iIntros (HP Hexe ?) "[#Hinv He]".
        rewrite /spec_ctx /tpool_pointsto.
        iDestruct "Hinv" as (ei si) "Hspec".
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]".
        (* two assignments to own config_name *)
        Check prod_included.
        iCombine "Hown He" gives "%fo".
        apply auth_both_valid_discrete in fo as [hm hmm].
        Check prod_included.
        apply prod_included in hm as [foo _]. simpl in foo. 
        Check singleton_included_l {[0 := Excl ei']} 0 (Excl (fill K e)).
        apply singleton_included_l in foo as [e'' [f g]].
        Check lookup_singleton.
        rewrite lookup_singleton in f.
        rewrite -f in g.
        apply Excl_included in g.
        Check own_update_2.
        unfold spec_inv.
        iModIntro.
        iSplitL "Hown".
        {
         iModIntro.
         iExists ei' , si'.
         iSplit. done. done.   
        }
        iModIntro.

    Admitted.

    Lemma do_step_pure E  K e e' `{!PureExec True 1 e e'}:
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
    Proof. by eapply step_pure'; last eauto. Qed.

    (*  cant return auth ownership because 
    that resource is needed to restore the invariant
     *)
    Lemma do_step_new E K t : 
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K (New t) ={E}=∗ ∃ s : list loc,
        own config_name  
        (◯ ({[0 := Excl (fill K (Case (fresh s)))]}, list_to_set (fresh s :: s))).
    Proof.
        iIntros (?) "[#Hsctx Hexe]".
        (* Recall definition of spec_ctx
            spec_ctx := (∃ e s, inv specN (spec_inv e s))%I.
        *)
        iDestruct "Hsctx" as (ei si) "Hspec".
        (* Recall definition of spec_inv
           
            Definition spec_inv (e : expr)(s : state) : iProp Σ := 
                (∃ e' s', 
                    own config_name (● ({[ 0 := Excl e']} , (list_to_set s')))
                    ∗ ⌜rtc erased_step ([e],s) ([e'],s')⌝)

            There is some future expression e' and program state s'
            such that configuration (e',s') is reachable by (e,s)
        
            Open the invariant
        *)
        iInv specN as ">[%ei' [%si' [Hown %Hrtc]]]".
        (* By opening the invariant, 
        We obtain the following data
            (e',s')
            rtc erased_step ([ei], si) ([ei'], si')
            own config_name (● ({[0 := Excl ei']}, list_to_set si'))

            since we have fill K (New t) as an assumption
                we know that e' is equal to (fill K (New t))
                This is proved with iCombine 
                and properties of the involved cameras

        in addition to showing the original goal
            ∃ s : list loc ,
                own config_name  
                    (◯ ({[0 := Excl (fill K (Case (fresh s)))]}, {[fresh s]}))

        we must also restablish the invariant namely 
            Definition spec_inv (e : expr)(s : state) : iProp Σ := 
                (∃ e' s', 
                    own config_name (● ({[ 0 := Excl e']} , (list_to_set s')))
                    ∗ ⌜rtc erased_step ([e],s) ([e'],s')⌝)

        What we want to do here is chose a new e' and s'
            namely (fill K (Case (fresh s'))), {[fresh s']} union s'

        Show that we can reduce to this new configuration
        Additionally, we need to update the resources
        
        *)
        (* first, establish the fact that e' = fill K (New t) *)
            rewrite /spec_ctx /tpool_pointsto. 
        iCombine "Hown Hexe" gives
        %[[Htpj _]%prod_included ?]
            %auth_both_valid_discrete.
        simpl in Htpj.
        apply singleton_included_l in Htpj as [e'' [f g]].
        Check lookup_singleton.
        rewrite lookup_singleton in f.
        rewrite -f in g.
        apply Excl_included in g. symmetry in g.
        assert (ei' = fill K (New t)) by done; subst.
        (* Now we have e' = fill K (New t)  and 
        
            "Hexe" : own config_name 
                        (◯ ({[0 := Excl (fill K (New t))]}, ∅))    
            "Hown" : own config_name 
                        (● ({[0 := Excl (fill K (New t))]}, list_to_set s'))

            Lets first demonstrate that we can step to (fill K (Case (fresh s')))
                given that we have
                    rtc erased_step (e, s) (fill K (New t), s')
                    and we can base step
                        (New t) ~~> (Case (fresh s'))
        *)
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

        iMod (own_update_2 with "Hown Hexe") as "[Hauth Hview]".
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
            rewrite H3. 
            destruct mz ; simpl ; set_solver.
        }
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
        (* With the invariant reestablished, 
            now we can now show our "post condition"  *)
        iModIntro.
        iExists si'.
        iApply "Hview".
    Qed.

    Lemma uhg E K (s s' : list loc) :
    nclose specN ⊆ E →
    spec_ctx ∗
        own config_name (● ({[0 := Excl (fill K (Case (fresh s)))]}, list_to_set s')) ={E}=∗
        False %I.
    (*     own config_name (● ({[0 := Excl (fill K (Case (fresh s)))]}, union ({[fresh s]}) (list_to_set s))).
    *) Proof.
        iIntros "%specN [#Hctx Hcfg]".
        iDestruct "Hctx" as (ei si) "Hspec".
        iInv "Hspec" as ">[%ei' [%si' [Hown %Hrtc]]]".

        iCombine "Hown Hcfg" gives "%huh".
        (*  BAD 
            threading ownership of config state allows derivation of false 
        *)
        destruct huh. simpl in *.
        apply dfrac_valid_own_r in H0.
        exfalso.
        done.
    Qed.
(*     
        apply auth_auth_op_validN in huh.
        apply auth_auth_dfrac_op_inv  in huh.
        assert (ei' = (fill K (Case (fresh s)))).
        {   
           inversion huh. simpl in H0.
           set_solver. 
       }
       assert ((list_to_set si') ≡ ((list_to_set s') : gset  loc)). {
        inversion huh. apply H2.
       }
       iModIntro.
       iSplitL "Hown".
       - unfold spec_inv. iModIntro.
       iExists ei' ,si'.
       iSplit. done. done.
       - (* just demonstrate that the state has to be a certain form *)

       rewrite H0 in Hrtc.
       apply rtc_inv_r in Hrtc.

       inversion Hrtc.
       + rewrite H4 in Hrtc. rewrite H5 in Hrtc.
       apply rtc_inv_r in Hrtc as [none | ind].
       {
        admit.
       }
       d
       apply erased_steps_nsteps in Hrtc as [n [ks stp]].
       destruct stp.
       { (* no steps taken *)

        }
       Print erased_step.
       Print rtc. 
       Check rtc_r.
        admit.
       +
       -

        rewrite -auth_auth_dfrac_op in huh.
        gives
        %[[Htpj _]%prod_included ?]
            %auth_both_valid_discrete.
        simpl in Htpj.
        apply singleton_included_l in Htpj as [e'' [f g]].
        Check lookup_singleton.
        rewrite lookup_singleton in f.
        rewrite -f in g.
        apply Excl_included in g. symmetry in g.
        assert (ei' = fill K (New t)) by done; subst. *)

    Lemma step_fst E  K e1 v1 e2 v2 :
        to_val e1 = Some v1 → 
        to_val e2 = Some v2 → 
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K (Fst (Pair e1 e2)) ={E}=∗ ⤇ fill K e1.
    Proof. by intros; apply: do_step_pure. Qed.

    Lemma step_snd E  K e1 v1 e2 v2 :
        to_val e1 = Some v1 → 
        to_val e2 = Some v2 → 
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K (Snd (Pair e1 e2)) ={E}=∗ ⤇ fill K e2.
    Proof. by intros; apply: do_step_pure. Qed.

    Lemma step_caseOf_true E K l e2 e3 e4 v2: 
        to_val e2 = Some v2 →
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K (CaseOf (Inj (Case l) e2) (Case l) e3 e4)  ={E}=∗ ⤇ fill K e3.[e2/].
    Proof.
        intros. apply do_step_pure.
        -  apply wp_case_match. exists v2. apply of_to_val. done.
        - done.
    Qed. 

    Lemma step_caseOf_false E K l l' e2 e3 e4 v2: 
        to_val e2 = Some v2 →
        nclose specN ⊆ E →
        l <> l' →
        spec_ctx ∗ ⤇ fill K (CaseOf (Inj (Case l) e2) (Case l') e3 e4)  ={E}=∗ ⤇ fill K e4.
    Proof.
        intros. apply do_step_pure.
        -  apply wp_case_nomatch. exists v2. apply of_to_val; done. done.
        -done.
    Qed. 

End cfg.



        (* 
    

(* need to enhance state.. *)
Class logrelSig  Σ := Resources {
    invariants : invGS Σ;
    predicates :: savedPredG Σ (val * val) ;
    names :: gset_bijG Σ loc loc ;
    name_set : gname
}.
Check rtc.
Check erased_step. 
Locate erased_step.
Check gset_bijR.

Check authR.
Definition combine (l1 l2 : list loc) : gset (loc * loc) := 
    list_to_set (zip l1 l2).

(* not sure about the camera for the expression ..
   want a unital camera    *)
Definition spec_thread : cmra := exclR exprO.
(* Definition tpoolUR : ucmra := gmapUR nat (exclR exprO).
 *)

 (* The data for our ghost execution
 it is the program itself and a bijection of locations it maintains as program state? *)
 Definition configRA : cmra := prodR spec_thread (gset_bijR loc loc).

Definition as_thread (e : expr) : spec_thread := Excl e.

Class configSpec Σ := CS { 
    config_in :: inG Σ configRA ; 
    spec_predicates :: savedPredG Σ (val * val) ;
    config_name : gname
}.

Section definitionsS.
    Context `{configSpec Σ, invGS Σ}.
    (* This is similar to the state interpretation in the unary relation
     
    For some expression e in program state s,
        There exists some (e',s') with logical state s'log reachable from (e,s)
        such that
            there is a bijection between s' and s'log in the ghost state
            and for every l in s'log, there is a value predicate

    wait.. shouldn't the ghost state now have value relations?
        or is that SystemG.. 
    *)
    Definition spec_inv (e : expr)(s : state) : iProp Σ := 
        (∃ e' s' s'log, own config_name (Excl e' , ●V (combine s' s'log))
                    ∗ [∗ list] l' ∈ s'log, (∃ (P : D), saved_pred_own l' (DfracDiscarded) P)
                    ∗ ⌜rtc erased_step ([e],s) ([e'],s')⌝)%I.

    Definition spec_ctx : iProp Σ :=
        (∃ e s, inv specN (spec_inv e s))%I.

    Definition spec_points_to_pred (l' : loc)(P : @D Σ) : iProp Σ := 
        (∃ e l, 
            own config_name (Excl e, ◯V {[ (l, l') ]}) ∗
            saved_pred_own l' (DfracDiscarded) P)%I.

    Definition spec_pointer (e : expr) : iProp Σ := 
        own config_name (Excl e , ◯V empty).

End definitionsS.

Notation "l ↦ₛ P" := (spec_points_to_pred l P) (at level 20) : bi_scope.
Notation "⤇ e" := (spec_pointer e) (at level 20) : bi_scope.

Section cfg.
    Context `{logrelSig Σ, invGS Σ , configSpec Σ}.

    Check specN.
    Check fupd.
    Print coPset.
    Search coPset.
    Check nclose specN.
    Print UpClose.
    
    (* opening invariants  *)
    Lemma inv_open_fail  (N : namespace) (P Q : iProp Σ) :
        inv N (P) ⊢ Q.
    Proof.
        iIntros "Hinv".
        Fail iInv "Hinv" as "HP".
    Abort.

    Lemma inv_open_fail (N : namespace) (P Q : iProp Σ) `{!Persistent P}  :
        inv specN (P) ∗ (P -∗ Q)⊢ |={nclose specN}=> Q.
    Proof.
        iIntros "(Hinv & HPQ)".
        iInv "Hinv" as "#HP".
        iModIntro.
        iSplit. 
        - iApply "HP".
        - iModIntro. iApply "HPQ".  iLöb as "H".
    Abort.

    Lemma step_pure' E  K e e' (P : Prop) n :
        P →
        PureExec P n e e' →
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
    Proof.
        iIntros (HP Hexe ?) "[#Hinv He]".
        iDestruct "Hinv" as (ei si) "Hspec".
        iInv 
        iInv specN as (a b c) ">d" .




Definition state_interp `{logrelSig Σ} (s : list loc) : iProp Σ :=
    ∃ (s' : list loc ) , 
            gset_bij_own_auth name_set (DfracOwn 1) (combine s s')  ∗
            [∗ list] l' ∈ s', (∃ (P : D), saved_pred_own l' (DfracDiscarded) P).


Global Instance OSum_irisGS `{logrelSig Σ} : irisGS OSum_lang Σ := {
    iris_invGS := invariants;
    num_laters_per_step _ := 0;
    state_interp s  _ _ _ := state_interp s;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.
 *)