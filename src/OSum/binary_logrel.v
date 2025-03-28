From stdpp Require Import base gmap coPset tactics proof_irrel.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map gset_bij.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.

From MyProject.src.OSum Require Export OSum persistent_pred wp_rules binary_rules.

Definition logN : namespace := nroot .@ "logN".

Class RelationResources Σ := RelRes{
    predicates :: savedPredG Σ (val * val) ;
    rel_bijection :: gset_bijG Σ (loc * loc) loc ;
    name_bijection :: gset_bijG Σ loc loc;
    sets :: inG Σ (authR (gsetUR loc))
}.

Class relStore  Σ  := RelStore {
    resources :: RelationResources Σ ; 
    rel_bij : gname ;
    name_bij : gname; 
    name_set : gname
}.

Class logrelSig Σ := LogRelSig {
    invariants : invGS Σ;
    store :: relStore  Σ ;
}.


Definition combine {A}{B}`{Countable (A * B)}(l : list A)(l' : list B) : gset (A * B) := 
    list_to_set (zip l l').


    Lemma not_in_combine_left {A}{B}`{Countable (A * B)}(l1 : list A)(l2 : list B) a b : 
    a ∉ l1 -> 
    (a , b) ∉ combine l1 l2 .
Proof.
    unfold not. intros.
    apply elem_of_list_to_set in H1.
    apply elem_of_zip_l in H1.
    apply H0. exact H1. 
Qed.

    Lemma not_in_combine_right {A}{B}`{Countable (A * B)}(l1 : list A)(l2 : list B) a b : 
        b ∉ l2 -> 
        (a , b) ∉ combine l1 l2 .
    Proof.
        unfold not. intros.
        apply elem_of_list_to_set in H1.
        apply elem_of_zip_r in H1.
        apply H0. exact H1. 
    Qed.

    Lemma adjust_combine {A B}`{Countable (A * B)}{L1 L2} a b :
        a ∉ L1 -> 
        b ∉ L2 -> 
        {[(a, b)]} ∪ combine L1 L2 = combine (a :: L1) (b :: L2).
    Proof.
        intros.
        rewrite set_eq.
        intros (a' , b').
        split.
        - intros. 
        destruct (decide ((a , b) = (a' , b'))).
        {
            inversion e. subst.
            apply elem_of_list_to_set.
            rewrite (zip_with_app pair [a'] L1 [b'] L2 eq_refl).
            constructor.
        }
         apply elem_of_list_to_set.
        pose proof (zip_with_app pair [a] L1 [b] L2 eq_refl).
        rewrite H3.
        apply elem_of_list_further.
        pose proof ( elem_of_union {[(a, b)]} (combine L1 L2) (a' , b')).
        apply H4 in H2.
        destruct H2.
        +        assert ( (a , b) <> (a' , b')). {
            unfold not. intros. inversion H5. apply n. done.
        }
        rewrite elem_of_singleton in H2. symmetry in H2. contradiction.
        + unfold combine in H2.            
         apply elem_of_list_to_set in H2. exact H2.
        -
        intros.
        unfold combine in H2. apply elem_of_list_to_set in H2.
        simpl in H2.
        unfold combine.
        Search list_to_set.
        rewrite <- list_to_set_cons.
        apply elem_of_list_to_set. exact H2.
    Qed.



Definition D `{ts : !relStore Σ}:= persistent_pred (val * val) (iProp Σ).

Definition state_interp  `{relStore Σ}`{configSpec Σ}(s : list loc) : iProp Σ :=
    ∃ (s' s'': list loc ) , 
        own config_name (◯ (None, list_to_set s')) ∗
        gset_bij_own_auth name_bij (DfracOwn 1) (combine s s') ∗
        gset_bij_own_auth rel_bij (DfracOwn 1) (combine (zip s s') s'') ∗
        [∗ list] l ∈ s'', (∃ (P : D), saved_pred_own l (DfracDiscarded) P).
(*     
    ∃ (s' s'' : list loc ) , 
(*         own config_name (◯ (empty, list_to_set s')) ∗
 *)        gset_bij_own_auth name_bij (DfracOwn 1) (combine s s') ∗
        gset_bij_own_auth rel_bij (DfracOwn 1) (combine (zip s s') s'') ∗
        [∗ list] l ∈ s'', (∃ (P : D), saved_pred_own l (DfracDiscarded) P).
     ∀ (s' : list loc), gset_bij_own_auth name_bij (DfracOwn 1) (combine s s') -∗
    ∃ (s'' : list loc ) ,         
        gset_bij_own_auth rel_bij (DfracOwn 1) (combine (zip s s') s'') ∗
        [∗ list] l ∈ s'', (∃ (P : D), saved_pred_own l (DfracDiscarded) P). *)

(*     ∃ (s' s'' : list loc ) , 
        gset_bij_own_auth name_bij (DfracOwn 1) (combine s s') ∗
        gset_bij_own_auth rel_bij (DfracOwn 1) (combine (zip s s') s'') ∗
        [∗ list] l ∈ s'', (∃ (P : D), saved_pred_own l (DfracDiscarded) P).
        *)

(*     own name_set (● (list_to_set s)). *)

(* Definition state_elem `{ts : !relStore Σ} (l : loc) : iProp Σ :=
    own name_set (◯ (singleton l)).

Notation "l ∈i" := (state_elem l) (at level 20) : bi_scope. *)


Global Instance OSum_irisGS `{logrelSig Σ}`{configSpec Σ} : irisGS OSum_lang Σ := {
    iris_invGS := invariants;
    num_laters_per_step _ := 0;
    state_interp s  _ _ _ := state_interp s;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section binary_logrel.
    Context`{logrelSig Σ, configSpec Σ}.

    Definition VRel := listO D -n> D.

    Program Definition pointsto_def (l l' : loc) : D -n> iPropO Σ  :=
    λne R, (∃ (l'' : loc), 
            gset_bij_own_elem name_bij l l'  ∗
            gset_bij_own_elem rel_bij (l , l') l''  ∗ 
            saved_pred_own l'' DfracDiscarded R)%I.
    Next Obligation. Admitted.

    Notation "l @ l' ↦□ R" := (pointsto_def l l' R)
    (at level 20,  format "l @ l' ↦□ R") : bi_scope.

    Instance mypointsto_persist (l l': loc)  (R : D) : Persistent (l @ l' ↦□ R).
    apply _. Qed.

    Definition interp_expr (τi :  VRel) (Δ : listO D) (ee : expr * expr) : iProp Σ := 
    (∀ K, ⤇ fill K (ee.2) -∗
        WP ee.1 {{ v, ∃ v', ⤇ fill K (of_val v') ∧ τi Δ (v, v') }})%I.

    Global Instance interp_expr_ne n :
        Proper (dist n ==> dist n ==> (=) ==> dist n) interp_expr.
    Proof. unfold interp_expr; solve_proper. Qed.

    
    Program Definition interp_TVar (v : var) : VRel := 
        λne rho, PersPred (default (inhabitant : persistent_pred _ _) (rho !! v)).
    Solve Obligations with repeat intros ?; simpl; solve_proper.

    Program Definition interp_TUnit : VRel := 
    λne rho, PersPred(fun w => ⌜w.1 = UnitV /\ w.2 = UnitV⌝%I).

    Definition interp_TInt : VRel := 
    λne rho, PersPred(fun w =>(∃ (z : Z), ⌜w.1 = IntV z /\ w.2 = IntV z⌝))%I.

    Definition interp_TBool : VRel := 
    λne rho, PersPred(fun w => (∃ (b : bool), ⌜w.1 = BoolV b /\ w.2 = BoolV b⌝))%I.

    Program Definition interp_TProd (interp1 interp2 : VRel) : VRel := 
        λne rho, PersPred(fun w => (∃ vv1 vv2 , 
            ⌜w = (PairV vv1.1 vv2.1 ,PairV vv1.2 vv2.2)⌝  ∧ 
            interp1 rho vv1  ∧ 
            interp2 rho vv2))%I.  
    Solve Obligations with solve_proper.

    Definition case_inv (l l' : loc)(R : D): iProp Σ := 
(*         state_elem l ∧
        spec_state_elem l' ∧  *)
        l @ l' ↦□ R.

    Program Definition interp_TCase (interp : VRel) : VRel := 
        λne rho, PersPred(fun w => 
            ∃ (l l' : loc), 
                ⌜w = (CaseV l , CaseV l')⌝ ∧
                inv (logN .@ (l,l')) (case_inv l l' (interp rho)))%I.
(*                 (case_inv l l' (interp rho)))%I.
 *)                (* can I get away with not using inv here? *)
(*                 inv (logN .@ (l,l')) (case_inv l l' (interp rho)))%I.
 *)    Next Obligation.  Admitted.

    Definition interp_TOSum : VRel := 
        λne rho, PersPred(fun w => 
            ∃ (l l' : loc)(v1 v2 : val)(R : D),
                ⌜w = (InjV (CaseV l) v1 , InjV (CaseV l') v2)⌝ ∧
                ▷ l @ l' ↦□ R ∧
                R (v1 ,v2))%I.

    Program Definition interp_TArrow (interp1 interp2 : VRel) : VRel :=
        λne Δ,
        PersPred
        (λ ww, □ ∀ vv, interp1 Δ vv →
                        interp_expr
                            interp2 Δ (App (of_val (ww.1)) (of_val (vv.1)),
                                        App (of_val (ww.2)) (of_val (vv.2))))%I.
    Solve Obligations with solve_proper.
      
    Program Definition interp_TForall (interp : VRel) : VRel :=
        λne Δ, PersPred(fun ww =>
            □ ∀ τi,
                interp_expr
                interp (τi :: Δ) (TApp (of_val (ww.1)), TApp (of_val (ww.2))))%I.
    Solve Obligations with solve_proper.

    Program Definition interp_TExist (interp : VRel) : VRel :=
        λne Δ,PersPred
            (λ ww, ∃ (τi : D) vv, ⌜ww = (PackV vv.1, PackV vv.2)⌝ ∗
               interp (τi :: Δ) vv)%I.
    Solve Obligations with repeat intros ?; simpl; solve_proper.

    Fixpoint interp (τ : type) : VRel :=
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

    Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).


    Definition interp_env (Γ : list type)
    (Δ : list D) (vs : list (val * val)) : iProp Σ :=
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
        - 
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
        - 
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


End binary_logrel.

Global Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).