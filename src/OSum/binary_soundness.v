
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
Require Import Autosubst.Autosubst.


From MyProject.src.OSum Require Export OSum binary_logrel binary_fundamental binary_rules.

Class capabilities Σ := Cap {
  invs :: invGpreS Σ;
  res :: RelationResources Σ ;
}.

Definition soundness_binaryΣ : gFunctors := #[ GFunctor (authR configRA) ].

(* FIXME: Really we should define a [soundnessG] as well. *)
Global Instance inG_soundness_binaryΣ Σ : subG soundness_binaryΣ Σ → inG Σ (authR configRA).
Proof. solve_inG. Qed.


Lemma basic_soundness Σ `{capabilities Σ, inG Σ (authR configRA)}
    e e' τ v s :
  (∀ `{logrelSig Σ, configSpec Σ}, ⊢ [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], []) ([of_val v], s) →
  (∃ s' v', rtc erased_step ([e'], []) ([of_val v'], s')).
Proof.
    intros Hlog Hstep.
    Check (adequate NotStuck e [] (fun _ _ => exists s v, rtc erased_step ([e'],[]) ([of_val v], s))).
    cut (adequate NotStuck e [] (fun _ _ => exists s v, rtc erased_step ([e'],[]) ([of_val v], s))).
    { destruct 1. naive_solver. }
    eapply (wp_adequacy Σ _). simpl.
    iIntros (Hinv ?).
    Print binary_logrel.state_interp.
    iExists (fun s _ => binary_logrel.state_interp s), (fun _ => True%I).
    iSplitL.
    iPoseProof ((Hlog _ _ )) as "Hrel".
    iSpecialize ("Hrel" $! [][] with "[]").
    {
        iSplit.
        - iExists e' ,[]. admit.
        - iApply (@interp_env_nil _ _ _).
    }
    simpl.
    replace e with e.[env_subst[]] at 2 by by asimpl.
    
    Check adequate.
