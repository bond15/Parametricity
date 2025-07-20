
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import gset_bij .
Require Import Autosubst.Autosubst.

From MyProject.src.OSum Require Export unary_fundamental.

(*
  "adequate" 
      Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
      (φ : val Λ → state Λ → Prop) := {
        adequate_result t2 σ2 v2 :
            rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → 
            φ v2 σ2;
        adequate_not_stuck t2 σ2 e2 :
            s = NotStuck →
            rtc erased_step ([e1], σ1) (t2, σ2) →
            e2 ∈ t2 → 
            not_stuck e2 σ2
      }.

      has two fields, (we only care about the second one for the moment)
      stating that given any epression e1 and state σ1, 
        whenever e1 with program state σ1 evaluates to an expression e2 with program state σ2
        the program is not stuck
          meaning e2 is either a value or it can be reduced further

        where

          Definition not_stuck (e : expr Λ) (σ : state Λ) :=
            is_Some (to_val e) ∨ reducible e σ.
          Definition reducible (e : expr Λ) (σ : state Λ) :=
            ∃ κ e' σ' efs, prim_step e σ κ e' σ' efs.

        Note that prim_step is the base reduction a user gives in the definition of "Language"

  We want to show that any well typed OSum_lang program e with the empty program state [] 
  is safe to evaluate.
 *)

Class capabilities Σ := Cap {
  invs :: invGpreS Σ;
  configSpec Σ
  res :: RelationResources Σ ;
}.

(* Any execution of e starting in the empty program state should not become stuck.
    I demand e start in an empty program state here.
    e could start in an arbitrary program state s
      in order to state this, we'd have to construct a ghost state from program state s
      This would require additional information not in s, specifically |s| many predicates on "val"

    In the case [] ⊢ₜ e : τ,
      e is a closed term that can't use any predicates in the ghost state
        it might as well be empty
      The only syntactically well-typed way to introduce a case symbol is from the 
      expression "New t" which is guarunteed to generate a case that is fresh.
*)
Definition safe (e : expr) := 
  forall e' s', rtc erased_step ([e], []) ([e'], s') → not_stuck e' s'.

Theorem adequacy_of_semantic_typing `{capabilities Σ}(e : expr) (t : type) : 
  (∀ `{logrelSig Σ}, ⊢ [] ⊨ e : t) -> safe e.
Proof.
  intros semtyped.
  (* adequacy of WP for OSum_lang is enough to prove this *)
  enough (adequate NotStuck e [] (fun _ _ => True)) as [_ notStuck].
  - (* assuming adequacy of WP for OSum_lang 
      simply use the field "adequate_not_stuck" of "adequacy"  *)
    unfold safe ;intros e' s' reduces. 
    pose proof (notStuck [e'] s' e' eq_refl reduces).
    apply H0.
    apply elem_of_list_singleton.
    done.
  - (* Now we have to prove adequacy 
    which via "wp_adequacy_gen", it is sufficient to show 
    "state_interp [] ∗ WP e {{ _, True }}" *)
  eapply wp_adequacy_gen; simpl.
  + (* summon the invariant instance *)
  apply _.
  + intros Hinv ks.
  (* allocate an empty type store *)
  iMod (init_state) as "[%ts stInterp]".
  iModIntro.
  (* these have to be the same state_interp and fork_post used in the semantic typing proof 
    otherwise the proof won't go through since the implicits to wp dont align.
    You can see this if you set this flag and unfold definitions
      Set Printing Implicit. 
  *)
  iExists (fun s _ =>state_interp s).
  iExists (fun _ => True%I).
  (* It is easy to prove the state_interp for the empty program state *)
  iSplitL. { done. }
  (*  to prove  WP e {{ _, True }}, we can just use ⊢ [] ⊨ e : t
      this is because we can apply empty rho and empty gamma to  ⊢ [] ⊨ e : t 
      which boils down to WP e {{ v, interp t [] v }},
  *)
  (* in order to use ⊢ [] ⊨ e : t 
  we need to have a concrete instance of ghost state, logSigΣ 
  we need to adjust the post condition,
  and we need to massage e *)
  set (logSigΣ := LogRelSig Σ Hinv ts).
  replace e with e.[env_subst[]] by by asimpl.
  iApply wp_wand. { 
    (* just apply the fact that e is well typed *)
  iApply (semtyped logSigΣ $! [] [] ). iApply interp_env_nil. }
  eauto.
Qed.
 
(* what kind of typeclass magic is going on here? *)
Definition gen_ResΣ : gFunctors := #[savedPredΣ val ; gset_bijΣ loc loc].

Global Instance subG_ResΣ {Σ} : subG gen_ResΣ Σ → RelationResources Σ.
Proof. solve_inG. Qed.

(* Example foo : sigT RelationResources .
set (Σ' := #[gen_ResΣ ]).
exists Σ'.
apply _.
Qed. *)

Corollary type_soundness e τ  :
  [] ⊢ₜ e : τ → safe e.
Proof.
  intros ?. 
  (* chose the exact gFunctors / capabilities, 
  namely invariants, bijection, and saved pred *)
  set (Σ := #[invΣ ; gen_ResΣ]). 
  (* make a "capabilities Σ" instance to apply above result*)
  set (C := (Cap Σ _ _)).
  eapply (@adequacy_of_semantic_typing Σ C). 
  intros. apply fundamental. exact H.
Qed.
