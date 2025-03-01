From stdpp Require Import base gmap.

From iris.base_logic Require Import invariants iprop upred saved_prop.
From iris.base_logic.lib Require Import gset_bij .
From iris.algebra Require Import gset_bij excl gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.OSum Require Export OSum persistent_pred wp_rules.

Definition specN := nroot .@ "spec".



Definition D `{Σ : gFunctors}:= persistent_pred (val * val) (iProp Σ).

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


Definition combine (l1 l2 : list loc) : gset (loc * loc) := 
    list_to_set (zip l1 l2).

Definition spec_thread : cmra := exclR exprO.
Definition configRA : cmra := prodR spec_thread (gset_bijR loc loc).

Definition as_thread (e : expr) : spec_thread := Excl e.

Class configSpec Σ := CS { 
    config_in :: inG Σ configRA ; 
    spec_predicates :: savedPredG Σ (val * val) ;
    config_name : gname
}.

Section definitionsS.
    Context `{configSpec Σ, invGS Σ}.
    Definition spec_inv (ρ : cfg OSum_lang) : iProp Σ := 
        (∃ e s s', own config_name (Excl e , ●V (combine s s'))
                    ∗ [∗ list] l' ∈ s', (∃ (P : D), saved_pred_own l' (DfracDiscarded) P)
                    ∗ ⌜rtc erased_step ρ ([e],s)⌝)%I.

    Definition spec_ctx : iProp Σ :=
        (∃ ρ, inv specN (spec_inv ρ))%I.
    
End definitionsS.



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
