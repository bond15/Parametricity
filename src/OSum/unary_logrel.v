From stdpp Require Import base gmap coPset tactics proof_irrel.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map gset_bij.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.OSum Require Export OSum persistent_pred wp_rules.


(*  dumb

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  #[local] gen_heapGpreS_heap :: ghost_mapG Σ L V;
  #[local] gen_heapGpreS_meta :: ghost_mapG Σ L gname;
  #[local] gen_heapGpreS_meta_data :: inG Σ (reservation_mapR (agreeR positiveO));
}.

Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  #[local] gen_heap_inG :: gen_heapGpreS L V Σ;
  gen_heap_name : gname;
  gen_meta_name : gname
}.*)

Class RelationResources  Σ := RelRes{
    predicates :: savedPredG Σ val ;
    bijection :: gset_bijG Σ loc loc ;
}.

Class typeStore  Σ  := TypeStore {
    resources :: RelationResources Σ ; 
    name_set : gname
}.

Class logrelSig Σ := LogRelSig {
    invariants : invGS Σ;
    store :: typeStore  Σ 
}.

(* Class logrelSig  Σ := Resources {
    invariants : invGS Σ;
    predicates :: savedPredG Σ val ;
    names :: gset_bijG Σ loc loc ;
    name_set : gname
}. *)

    
    Definition D `{ts : !typeStore Σ}:= persistent_pred val (iProp Σ).

    Definition combine (l1 l2 : list loc) : gset (loc * loc) := 
        list_to_set (zip l1 l2).

    Definition state_interp  `{ts : !typeStore Σ}(s : list loc) : iProp Σ :=
        ∃ (s' : list loc ) , 
                gset_bij_own_auth name_set (DfracOwn 1) (combine s s')  ∗
                [∗ list] l' ∈ s', (∃ (P : D), saved_pred_own l' (DfracDiscarded) P).


Lemma init_state' {Σ : gFunctors}`{!RelationResources Σ}: 
    ⊢@{ iProp Σ } |==> 
        ∃ g : gname, 
            let ts := TypeStore Σ _ g in 
            @state_interp Σ ts [].
Proof.
    iMod (gset_bij_own_alloc_empty) as (g') "bij".
    iModIntro.
    iExists g'.
    iAssert (@state_interp Σ (TypeStore Σ _ g') []) with "[bij]" as "[%s' (P & Q)]".
    {
        iExists []. unfold empty. simpl. iSplitL ; done. 
    } simpl.
    unfold state_interp. iExists s'. iFrame.
Qed.

Lemma init_state {Σ : gFunctors}`{!RelationResources Σ}: 
    ⊢@{ iProp Σ } |==> 
        ∃ ts : typeStore  Σ ,  
            @state_interp Σ ts [].
Proof.
    iMod (init_state') as "[%g s]".
    iModIntro. iExists (TypeStore Σ _ g ). 
    iApply "s".
Qed.




Global Instance OSum_irisGS `{logrelSig Σ} : irisGS OSum_lang Σ := {
    iris_invGS := invariants;
    num_laters_per_step _ := 0;
    state_interp s  _ _ _ := state_interp s;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section unary_logrel.
    Context`{logrelSig Σ}.

    (* 
    
    persistent predicates state that the proposition P holds 
    over the sharable parts (core) of the resource

    Local Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
        {| uPred_holds n x := P n (core x) |}.


    Class Persistent {PROP : bi} (P : PROP) := 
        persistent : P ⊢ □ P.

    do we need to save persistent predicates instead of predicates ..? 
     *)
     

    Lemma convert (n : nat)(x y : D) : 
        @dist_later D (ofe_dist D) n x y -> 
        @dist_later (val -d> iPropO Σ) (ofe_dist (val -d> iPropO Σ)) n x y.
    Proof.
        intros. split. intros. apply H0. exact H1.
    Qed.

    (*  can I add this to a hint database so solve_proper picks up on it ?
    https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/stdpp/tactics.v
     *)
    Local Instance saved_persistent_pred_ne (l : loc) : 
        NonExpansive (λ P : D, saved_pred_own (encode l) DfracDiscarded P).
    Proof.
        eapply contractive_ne.
        red. red. intros.
        eapply saved_pred_own_contractive.
        apply convert. 
        done.
    Qed.

    Import uPred.
    (* This just says that there are two locations in bijection 
        and the second location stores a persistent predicate on values 
        
        using a view element for the bijection, not the authoritative element
    *)
    Local Program Definition pointsto_def (l l' : loc) : D -n> iPropO Σ  :=
        λne P, (gset_bij_own_elem name_set l l' ∗ saved_pred_own l' (DfracDiscarded) P)%I.
    Next Obligation.
        intros l.
        red. red. intros.
        eapply uPred_primitive.sep_ne.
        - solve_proper.
        -  eapply saved_persistent_pred_ne. exact H0.
    Qed.
          
    Local Notation "l @ l' ↦□ v" := (pointsto_def l l' v)
        (at level 20,  format "l @ l' ↦□ v") : bi_scope.

    Global Instance mypointsto_persist (l l': loc)  (P : D) : Persistent (l @ l' ↦□ P).
    apply _. Qed.

    (* the type of each case of the unary logical relation *)
    Definition VRelType := listO D -n> D.

    Program Definition interp_TVar (v : var) : VRelType := 
        λne rho, PersPred (default (inhabitant : persistent_pred _ _) (rho !! v)).
    Solve Obligations with repeat intros ?; simpl; solve_proper.

    Program Definition interp_TUnit : VRelType := 
         λne rho, PersPred(fun v => ⌜v = UnitV⌝%I).

    Definition interp_TInt : VRelType := 
        λne rho, PersPred(fun v =>(∃ (z : Z), ⌜v = IntV z⌝))%I.

    Definition interp_TBool : VRelType := 
        λne rho, PersPred(fun v => (∃ (b : bool), ⌜v = BoolV b⌝))%I.

    Program Definition interp_TProd (interp1 interp2 : VRelType) : VRelType := 
        λne rho, PersPred(fun v => (∃ v1 v2 , ⌜v = PairV v1 v2⌝  ∗ interp1 rho v1  ∗ interp2 rho v2))%I.  
    Solve Obligations with solve_proper.

    Definition interp_TCase' (interp : VRelType)(rho : listO D) : D :=
        PersPred(fun v => (∃ l l' , ⌜v = CaseV l⌝ ∗ (l @ l' ↦□ (interp rho))))%I.

    Local Instance interp_TCase'_ne (interp : VRelType)(rho : listO D)  : 
        NonExpansive (PersPred(fun v => (∃ l l', ⌜v = CaseV l⌝ ∗ l @ l' ↦□ (interp rho)))%I).
    Proof.        
        solve_proper.
    Qed.

    (* solve_proper breaks here because saved_predicates are contractive
    There's probably a better way to do this.
    *)
    Program Definition interp_TCase (interp : VRelType) : VRelType := 
        λne rho, 
            PersPred(fun v => (∃ l l' , ⌜v = CaseV l⌝ ∗ (l @ l' ↦□ (interp rho))))%I.
    Next Obligation.
        intros ? ? ? ? ? . split. simpl. 
        intros.
        split.
        - intros.
        eapply uPred_holds_ne.
        4 :{ exact H3. }  2:{ done. } 2:{ exact H2. }
        apply exist_ne. red. intros.
        apply exist_ne. red. intros.
        apply sep_ne. { done. }
        apply sep_ne. { done. }
        (* the "issue" *)
        apply saved_pred_own_contractive.
        pose proof (ofe_mor_ne _ _ interp n x y H0).
        apply dist_dist_later in H4.
        destruct (decide (n = n')).
        + subst. apply symmetry. apply convert. done. 
        + assert (n' < n). {lia. }
        apply dist_dist_later.
        pose proof (dist_later_dist_lt _ _ _ _ H5 H4).
        apply symmetry.
        done.
        - intros.
        (* exact same proof... *)
        eapply uPred_holds_ne.
        4 :{ exact H3. }  2:{ done. } 2:{ exact H2. }
        apply exist_ne. red. intros.
        apply exist_ne. red. intros.
        apply sep_ne. { done. }
        apply sep_ne. { done. }
        apply saved_pred_own_contractive.
        pose proof (ofe_mor_ne _ _ interp n x y H0).
        apply dist_dist_later in H4.
        destruct (decide (n = n')).
        + subst. apply symmetry. apply convert. done. 
        + assert (n' < n). {lia. }
        apply dist_dist_later.
        pose proof (dist_later_dist_lt _ _ _ _ H5 H4).
        apply symmetry.
        done.
    Qed.

     
    Program Definition interp_TOSum : VRelType := 
        λne rho, PersPred(fun v =>(∃ l l' v' P , ⌜v = InjV (CaseV l) v'⌝ ∗ l @ l'  ↦□ P ∗ P v'))%I.

    Program Definition interp_TArrow (interp1 interp2 : VRelType) : VRelType := 
        λne rho, PersPred(fun v => 
            (□ ∀ v', interp1 rho v' → WP App (of_val v) (of_val v') {{ interp2 rho }}))%I.
    Next Obligation.
        intros i1 i2. solve_proper.
    Qed.

    (* normal forall, not fresh forall
       for fresh forall, would need to update saved predicate map? *)
    Program Definition interp_TForall (interp : VRelType) : VRelType := 
        λne rho, PersPred(fun v => 
            (□ ∀ τi : D, WP TApp (of_val v) {{ interp (τi :: rho) }}))%I.
    Next Obligation.
        intros i1. solve_proper.
    Qed.
    Check later_own.
    (* forall fresh would be something like...  *)
(*     Program Definition interp_FreshForall (interp : VRelType) : VRelType := 
        λne rho, PersPred(fun v => 
            (□ ∀ (P : D)(l : loc), |==> l ↦□ P →  WP (App (TApp (of_val v)) (Case l)) {{ interp (P :: rho) }} )
        )%I. (* guard P? *)
    Next Obligation.
        intros i1. solve_proper.
    Qed.
 *)
    Program Definition interp_TExist (interp : VRelType) : VRelType := 
        λne rho, PersPred(fun v => 
            (∃ (τi : D) v' ,  ⌜v = PackV v'⌝ ∗ interp (τi :: rho) v))%I.
    Next Obligation.
        intros i1. solve_proper.
    Qed.

    (* The full unary logical relation  *)
    Fixpoint interp (τ : type) : listO D -n> D :=
        match τ return _ with
        | TUnit => interp_TUnit
        | TInt => interp_TInt
        | TBool => interp_TBool
        | TProd τ1 τ2 => interp_TProd (interp τ1) (interp τ2)
        | TArrow τ1 τ2 => interp_TArrow (interp τ1) (interp τ2)
        | TVar x => interp_TVar x
        | TForall τ' => interp_TForall (interp τ')
        | TExist τ' => interp_TExist (interp τ')
        | TOSum => interp_TOSum
        | TCase t => interp_TCase (interp t)
        end.
    Notation "⟦ τ ⟧" := (interp τ).

    Definition interp_env (Γ : list type)
        (Δ : list D) (vs : list val) : iProp Σ :=
        (⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I.
    Notation "⟦ Γ ⟧*" := (interp_env Γ).

    Global Instance interp_env_base_persistent Δ Γ vs :
    TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
    Proof. revert vs; induction Γ => vs; destruct vs; constructor; apply _. Qed.
    Global Instance interp_env_persistent Γ Δ vs : Persistent (⟦ Γ ⟧* Δ vs) := _.


    Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
    Proof. iSplit; simpl; auto. Qed.

    Import uPred.
    Lemma interp_env_cons Δ Γ vvs τ vv :
        ⟦ τ :: Γ ⟧* Δ (vv :: vvs) ⊣⊢ ⟦ τ ⟧ Δ vv ∗ ⟦ Γ ⟧* Δ vvs.
    Proof.
        rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
        by apply sep_proper; [apply pure_proper; lia|].
    Qed.


    Definition interp_expr (τ : type) (rho : list D) (e : expr) : iProp Σ :=
        WP e {{ ⟦ τ ⟧ rho }}%I.

    Notation "⟦ τ ⟧ₑ" := (interp_expr τ).

    Lemma interp_env_length Δ Γ vs : ⟦ Γ ⟧* Δ vs ⊢ ⌜length Γ = length vs⌝.
    Proof. by iIntros "[% ?]". Qed.

    Lemma interp_env_Some_l Δ Γ vs x τ :
        Γ !! x = Some τ → ⟦ Γ ⟧* Δ vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⟦ τ ⟧ Δ v.
    Proof.
        iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
        destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
        { by rewrite -Hlen; apply lookup_lt_Some with τ. }
        iExists v; iSplit; first done. iApply (big_sepL_elem_of with "HΓ").
        apply elem_of_list_lookup_2 with x.
        rewrite lookup_zip_with; by simplify_option_eq.
    Qed.

    (*  need to fix this proof *)
    Lemma interp_weaken Δ1 Π Δ2 τ :
        ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
        ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
    Proof.
        revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto; intros ?; simpl.
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        Admitted.
    (*     - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        - f_equiv.
        apply fixpoint_proper=> τi w /=.
        by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
        { by rewrite !lookup_app_l. }
        rewrite !lookup_app_r; [|lia ..]; do 3 f_equiv; lia.
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    Qed. *)

    (* need to fix this proof  *)
    Lemma interp_subst_up Δ1 Δ2 τ τ' :
        ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
        ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
    Proof.
        revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto; intros ?; simpl.
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        Admitted. (* by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
        - f_equiv.
        apply fixpoint_proper=> τi w /=.
        by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - match goal with |- context [_ !! ?x] => rename x into idx end.
        rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
        { by rewrite !lookup_app_l. }
        rewrite !lookup_app_r; [|lia ..].
        case EQ: (idx - length Δ1) => [|n]; simpl.
        { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
        rewrite !lookup_app_r; [|lia ..]. do 3 f_equiv. lia.
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
        - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    Qed. *)

    (* fix this  *)
    Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
    Admitted.
    

End unary_logrel.

Global Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).