From stdpp Require Import base gmap.

From iris.base_logic Require Import invariants iprop upred saved_prop.
From iris.base_logic.lib Require Import gset_bij .
From iris.algebra Require Import gset_bij excl gmap gset cmra.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.


From MyProject.src.OSum Require Export OSum persistent_pred wp_rules.

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
    Admitted.

    Lemma do_step_pure E  K e e' `{!PureExec True 1 e e'}:
        nclose specN ⊆ E →
        spec_ctx ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
    Proof. by eapply step_pure'; last eauto. Qed.
    
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