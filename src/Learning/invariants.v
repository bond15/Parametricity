From stdpp Require Import base gmap coPset .
From Equations Require Import Equations.
From MyProject.src.OSum Require Export OSum.

From iris.algebra Require Import gmap_view coPset gset.
From iris.base_logic Require Import upred invariants iprop ghost_map wsat.
From iris.program_logic Require Export weakestpre lifting atomic ectx_lifting.
From iris.proofmode Require Import proofmode environments coq_tactics.


(* Dumb interpretation  *)
Module Dumb.
    Import OSum.
    (* sigma supports inv *)
    Context `(!invGS Σ).
    (* just one name for one instance of our heap *)
    Context (heap_name : gname).

    (* need a cmra for our state type  *)
    Print state. (* gmap loc type *)
    Print stateO. (* stateO = leibnizO state : ofe *)
    Check own.
    Print leibnizO.
    Print discreteO.

    (* use leibnizO to get an ofe on state := gmap loc type
      then agreeR to get a cmra on state
     *)
    Context `(inG Σ (agreeR (stateO))).

    Global Instance heapIG_irisG : irisGS OSum_lang Σ := {
    num_laters_per_step _ := 0;
    state_interp σ  _ _ _ := own heap_name (to_agree σ); 
    (* this is based off of gen_heap_interp
      Definition gen_heap_interp (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,
        
        ⌜ dom m ⊆ dom σ ⌝ ∗
        ghost_map_auth (gen_heap_name hG) 1 σ ∗
        ghost_map_auth (gen_meta_name hG) 1 m.
    *)
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
    }.

    Example e1 : expr := Bool true.

    Lemma first : ⊢@{iProp Σ} WP e1  {{ v, ⌜v = BoolV true⌝%I}}.
    Proof.  
        iApply wp_value.
        iPureIntro.
        reflexivity.
    Qed.


    Definition e2 : expr := BinOp Add (Int 1) (Int 2).

    Lemma second : ⊢@{iProp Σ} WP e2  {{ v, ⌜v = IntV 3⌝%I}}.
    Proof.
        iApply wp_lift_pure_det_base_step_no_fork.
        -(* prove e2 is not a value *) reflexivity.
        - simpl. (* given a state, prove you can take a base_step *)
         intros. repeat (eexists).
         eapply BinOpS  ; reflexivity.
        - (* prove you don't modify state, or fork 
        Todo this, need to use inversion on base_step *)
        intros.
        inversion H0.
        repeat (try split).
        inversion H4. inversion H10. rewrite <- H13 in H11. rewrite <- H14 in H11.
      simpl in H11. inversion H11. reflexivity. 
      - (* Now we need to show the next step that value 1+2 is 3 *)
       iModIntro.
       iModIntro.
       iModIntro.
       iIntros. (* I get a later credit to use ? *)
       iApply wp_value.
       iPureIntro.
       reflexivity.
  Qed.

  (*  ok, those are simple WP proofs ... 
    how about one with an invariant ?

    https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.invariants.html#inv_contractive
    API for invariants
  *)

  (* try hoare logic syntax *)
  Lemma test : {{{ True }}} e1{{{ v, RET v; True }}}.
  Abort.

  Check inv.
  Check inv_alloc.
  (* a namespace *)
  Let N := nroot .@ "myInvariant".
  Check N.

  Definition e3 : expr := New TBool (Int 7).

  Check own.
  Definition pointsto (l : loc)(ty : type) : iProp Σ := own heap_name (to_agree {[ l := ty]}).

Check fresh.
 Lemma alloc_fresh e v t σ :
    let l := fresh (dom σ) in
    to_val e = Some v → base_step (New t e) σ [] e (<[l:=t]>σ) [].
  Proof.
    intros.
    eapply NewS.
    - exact H0.
    - eapply (not_elem_of_dom(D:=gset loc)).
      eapply is_fresh.
Qed. 

  Lemma point : {{{ True }}} e3 {{{ (v : val), RET v; inv N (∃ (l : loc), pointsto l TBool) }}}.
  Proof.
    iIntros (phi _) "HPhi".
    unfold e3.
     iApply wp_lift_atomic_base_step_no_fork ; try reflexivity.
     iIntros (s1 ????) "Hsig".
     iModIntro. 
     iSplit.
  + iPureIntro; eexists _,_,_,_. 
    eapply alloc_fresh.  reflexivity. 
  + iNext.  iIntros (v2 sig2 efs Hstep) "lc".
  iModIntro. iSplit. Abort.

    (*           iMod (inv_alloc N _ (∃ l : loc, pointsto l TBool) ) as "Hinv". *)

     (*  iApply inv_alloc. *)

  
(* copying 
https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logrel/F_mu_ref_conc/wp_rules.v?ref_type=heads#L62*)
Lemma wp_alloc e v t  (l : loc) :
    IntoVal e v ->
    {{{ True%I }}} (New t e) {{{ (l : loc), RET v ; pointsto l t}}}.
Proof.
  intros ev.
  iIntros (Phi) "_ H".

  (*
    "H" : ▷ ∀ l0 : loc, pointsto l0 t -∗ Phi v 
    --------------------------------------∗ 
    WP New t e {{ v, Phi v }}

  *)
  iApply wp_lift_atomic_base_step_no_fork.
  - reflexivity.
  - iIntros (s1 ????) "Hsig".
  iModIntro.
  iSplit.
  + iPureIntro; eexists _,_,_,_. 
    eapply alloc_fresh. destruct ev. rewrite to_of_val. reflexivity. 
  + iNext. iIntros (v2 sig2 efs Hstep) "lc".
   iModIntro. inversion Hstep.
   iSplit.
   * iPureIntro. reflexivity.
   * (* Need to prove that the initial state interpretation implies the other state interpretation

          state_interp s1 ns ([] ++ κs) nt ⊢ state_interp (<[l0:=t]> s1) (S ns) κs nt 

        however, our state interpretation boils down to 
         
          own heap_name (to_agree s1) ⊢ own heap_name (to_agree (<[l0:=t]> s1))

          can we prove 
   
    *)
    iSplit. {
      simpl. try iApply own_update. Search (own). iApply (own_mono with "Hsig" ). unfold included. 
      exists (to_agree empty). simpl.
      
      
      
       Check own_update. admit. (* THIS should be provable, the maps should agree *)
    } destruct ev. simpl. rewrite <- H5. simpl. rewrite to_of_val. simpl. iApply ("H" $! l). unfold pointsto.
    (*  THIS is not provable, there is no update from s1 to a singleton 

          own heap_name (to_agree s1) ⊢ own heap_name (to_agree {[l := t]})

          demonstrating that our pointsto predicate 
              Definition pointsto (l : loc)(ty : type) : iProp Σ := own heap_name (to_agree {[ l := ty]}).

          is deficient
    
    *)
    Abort.



(*  Invariants via fancy update *)

Check fupd.
(*  indexed by two masks, which are sets of positive numbers *)


(* Definition of world satisfaction

  Definition wsat `{!wsatGS Σ} : iProp Σ :=
    locked (∃ I : gmap positive (iProp Σ),
      own invariant_name
        (gmap_view_auth (DfracOwn 1) (to_agree <$> (invariant_unfold <$> I))) ∗
      [∗ map] i ↦ Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})%I.
 *)

(* This lemma is located here
  https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.wsat.html#wsat_alloc

  it allocates the world satisfaction resource
 *)
Lemma wsat_alloc `{!wsatGpreS Σ} : ⊢ |==> ∃ _ : wsatGS Σ, wsat ∗ ownE ⊤.
Proof.
  iIntros.
  Check own_alloc.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI". admit.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ γI γE γD).
Abort.


End Dumb.

(* Authoratative camera *)
(* Use sets as a resource *)
Check coPset.
Check coPsetUR .
Check authR.


(*  use n%positive to parse numbers as positive binary numbers *)
Example s1 : coPset := singleton 9%positive ∪ singleton 7%positive.

Example sevenin : (7%positive) ∈ s1.
destruct (decide ((7%positive) ∈ s1)) ; reflexivity.
Qed.

Definition set : cmra := authR coPsetUR.
(* Definition authR (A : ucmra) : cmra := viewR (A:=A) (B:=A) auth_view_rel.

  Record view {A B} (rel : nat → A → B → Prop) :=
    View { view_auth_proj : option (dfrac × agree A) ; view_frag_proj : B }

  Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
    View (Some (dq, to_agree a)) ε.

  Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := 
    View None b.

  Notation "●V dq a" := (view_auth dq a)
  Notation "◯V a" := (view_frag a) (at level 20).
 *)

Definition s1_view : set := view_frag (singleton 7%positive).
Definition s1_auth : set := view_auth (DfracOwn (1/2)) s1.
(* but how are parts related to the whole ..?


  The view relation
  Definition auth_view_rel_raw {A : ucmra} (n : nat) (a b : A) : Prop :=
    (∃ c, a ≡{n}≡ b ⋅ c) ∧ ✓{n} a.
 *)
Eval red in (auth_view_rel_raw 7 s1_auth s1_view).
Example related (n : nat): auth_view_rel_raw n s1_auth s1_view.
Proof.
  unfold s1_auth; unfold s1_view.
  red.
  split.
  - unfold includedN. Abort.

(* so what is a ghost map? *)

Definition gm : cmra :=  (gmap_viewR nat (agreeR (leibnizO type))).
Check view_frag.
(* 
Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra :=
  viewR (gmap_view_rel K V).

    Canonical Structure viewR := Cmra (view rel) view_cmra_mixin.



Requirements of a view relation
    Structure view_rel (A : ofe) (B : ucmra) := ViewRel {
        view_rel_holds :> nat → A → B → Prop;
        view_rel_mono n1 n2 a1 a2 b1 b2 :
            view_rel_holds n1 a1 b1 →
            a1 ≡{n2}≡ a2 →
            b2 ≼{n2} b1 →
            n2 ≤ n1 →
            view_rel_holds n2 a2 b2;
        view_rel_validN n a b :
            view_rel_holds n a b → ✓{n} b;
        view_rel_unit n :
            ∃ a, view_rel_holds n a ε
        }.


The specific Gmap view relation
        Context (K : Type) `{Countable K} (V : cmra).
        Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
        Implicit Types (f : gmap K (dfrac × V)).

        Local Definition gmap_view_rel_raw n m f :=
            map_Forall (λ k fv,
            ∃ v dq, m !! k = Some v ∧ ✓{n} (dq, v) ∧ (Some fv ≼{n} Some (dq, v))) f.
            
Views
    Record view {A B} (rel : nat → (A : ofe) → (B : ucmra) → Prop) :=
    View { view_auth_proj : option (dfrac × agree A) ; view_frag_proj : B }.


    Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
        View (Some (dq, to_agree a)) ε.
                                     ^ unit of camear b
    Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := View None b.
    
    Notation "●V dq a" := (view_auth dq a)
    Notation "◯V a" := (view_frag a) 

 *)


Definition gmFun : gFunctors := ghost_mapΣ nat type.
Print ghost_map.


    (*
Lemma tac_wp_pure  Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => ??? HΔ'. rewrite into_laterN_env_sound /=.
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "Hwp !> _" => //.
Qed.

Ltac solve_vals_compare_safe :=
  
  fast_done || (left; fast_done) || (right; fast_done).

Lemma tac_wp_expr_eval  Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.


Ltac wp_expr_simpl := wp_expr_eval simpl.




Ltac wp_finish :=
  wp_expr_simpl.
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    (fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [tc_solve
      |try solve_vals_compare_safe
      |tc_solve
      |wp_finish
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"

    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Ltac wp_pures :=
  iStartProof;
  first [
          progress repeat (wp_pure _; [])
        | wp_finish
        ].
*)