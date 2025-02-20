From stdpp Require Import base gmap coPset tactics proof_irrel.

From iris.base_logic Require Import invariants iprop upred saved_prop gen_heap.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import cofe_solver gset gmap_view excl gset_bij.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.OSum Require Export OSum persistent_pred wp_rules.

Section logrel.
    Context`{logrelSig Σ}.

    (* 
    
    persistent predicates state that the proposition P holds over the sharable parts (core) of the resource

    Local Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
        {| uPred_holds n x := P n (core x) |}.


    Class Persistent {PROP : bi} (P : PROP) := 
        persistent : P ⊢ □ P.

    do we need to save persistent predicates instead of predicates ..? 
     *)
     
    Definition D := persistent_pred val (iProp Σ).

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
    Local Program Definition pointsto_def (l l' : loc) : D -n> iPropO Σ  :=
        λne P, (own name_set (gset_bij_elem l l') ∗ saved_pred_own l' (DfracDiscarded) P)%I.
    Next Obligation.
        intros l.
        red. red. intros.
(*         eapply uPred_primitive.exist_ne.
        red. intros s. *)
        eapply uPred_primitive.sep_ne.
        - solve_proper.
        -  eapply saved_persistent_pred_ne. exact H0.
    Qed.

(*     Local Program Definition pointsto_def (l : loc) : D -n> iPropO Σ  :=
        λne P, (∃ (s : state), ⌜l ∈ s⌝ ∗ own name_set s  ∗ saved_pred_own l (DfracDiscarded) P)%I.
    Next Obligation.
        intros l.
        red. red. intros.
        eapply uPred_primitive.exist_ne.
        red. intros s.
        eapply uPred_primitive.sep_ne.
        - solve_proper.
        - eapply uPred_primitive.sep_ne.
        + solve_proper.
        + eapply saved_persistent_pred_ne. exact H0.
    Qed.
 *)

(*     Local Definition pointsto_def (l : loc)  (P : D) : iProp Σ :=
        (∃ (s : state), ⌜l ∈ s⌝  ∗ own name_set s  ∗ saved_pred_own (encode l) (DfracDiscarded) P)%I.
 *)

    (*  why do i have goals of the form  Proper (dist n ==> dist n) ?
    where is this requirement coming from ? 
    
    This is how to state non,expansiveness
        Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).

        Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).


        does being contractive prove being non expansive?
            have f : X -> Y 
            ne := forall (n : nat)(x y : X), x ={n}= y -> f x ={n} f y

            contr := forall (n : nat)(x y : X), (forall m < n, x ={m}= y) -> f x ={n}= f y

        yes, proof is here
            https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#contractive

    *)

    Lemma contrIsNe {X Y : ofe}{f : X -n> Y}(c : Contractive f) : NonExpansive f.
    Proof.
        eapply contractive_ne. exact c.
    Qed.        


    Lemma persistant_pred_ne (P : D): NonExpansive P.
    Proof.
        solve_proper.
    Qed.
          
    Local Notation "l @ l' ↦□ v" := (pointsto_def l l' v)
        (at level 20,  format "l @ l' ↦□ v") : bi_scope.

    Global Instance mypointsto_persist (l l': loc)  (P : D) : Persistent (l @ l' ↦□ P).
    apply _. Qed.

    Definition VRelType := listO D -n> D.

    Program Definition interp_TVar (v : var) : VRelType := 
        λne rho, PersPred (default (inhabitant : persistent_pred _ _) (rho !! v)).
    Solve Obligations with repeat intros ?; simpl; solve_proper.

    Program Definition interp_TUnit : VRelType := 
         λne rho, PersPred(fun v => ⌜v = UnitV⌝%I).

    Definition interp_TInt : VRelType := 
        λne rho, PersPred(fun v =>(∃ (n : nat), ⌜v = IntV n⌝))%I.

    Definition interp_TBool : VRelType := 
        λne rho, PersPred(fun v => (∃ (b : bool), ⌜v = BoolV b⌝))%I.

    Program Definition interp_TProd (interp1 interp2 : VRelType) : VRelType := 
        λne rho, PersPred(fun v => (∃ v1 v2 , ⌜v = PairV v1 v2⌝  ∗ interp1 rho v1  ∗ interp2 rho v2))%I.  
    Solve Obligations with solve_proper.

    Definition interp_TCase' (interp : VRelType)(rho : listO D) : D :=
        PersPred(fun v => (∃ l l' , ⌜v = CaseV l⌝ ∗ l @ l' ↦□ (interp rho)))%I.

    Local Instance interp_TCase'_ne (interp : VRelType)(rho : listO D)  : 
        NonExpansive (PersPred(fun v => (∃ l l', ⌜v = CaseV l⌝ ∗ l @ l' ↦□ (interp rho)))%I).
    Proof.        
        eapply persistant_pred_ne.
    Qed.


    Check persistent_pred_car_ne val (iProp Σ) 0 (interp_TCase' _ _ )(interp_TCase' _ _ ) _ _  _ _. 
        
    Program Definition interp_TCase (interp : VRelType) : VRelType := 
         λne rho, interp_TCase' interp rho.
    Next Obligation.
        intro.
        red. red. intros.
        try rewrite persistent_pred_ext.
        pose proof (interp_TCase'_ne interp x ).
        pose proof (interp_TCase'_ne interp y ).
        pose proof (persistent_pred_car_ne val (iProp Σ) n (interp_TCase' interp x )(interp_TCase' interp y ) ).
    Admitted.
     


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



    Check upn.
    Eval compute in upn 2 Var 9. 
    Check ren.


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

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
 Admitted.
    

End logrel.

Global Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).


(* 



    (*  what is the core of our resouce ... 

    Local Instance dfrac_pcore_instance : PCore dfrac := λ dq,
        match dq with
        | DfracOwn q ⇒ None
        | DfracDiscarded ⇒ Some DfracDiscarded
        | DfracBoth q ⇒ Some DfracDiscarded
        end.
    

    what is the meaning of discarded... 
    
    Global Instance saved_pred_discarded_persistent γ Φ :
        Persistent (saved_pred_own γ DfracDiscarded Φ).
    Proof. apply _. Qed.

    Do I need to say it owns it, or can it just be discarded knowledge ...
        
    *)

    (* pure things are always persistent *)
    Definition p1 (l : loc) : iProp Σ := (∃ (s : state), ⌜l ∈ s⌝)%I.
    Local Instance pers_p1 (l : loc) : Persistent (p1 l).
    Proof.
        apply _.
    Qed.

    (*  note that
    
        Class CoreId {A : cmra} (x : A) := core_id : pcore x ≡ Some x.

        Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
        Proof. rewrite !own_eq /own_def; apply _. Qed.

        recall, state := gset loc

        hmm.. probably not where the instance is summoned from 
     *)

    Definition p2 : iProp Σ := (∃ (s : state), own name_set s )%I.
    Local Instance pers_p2 : Persistent p2.
    Proof.
        apply _.
    Qed.

    Definition p1p2 (l : loc):  iProp Σ := (∃ (s : state), ⌜l ∈ s⌝ ∗ own name_set s )%I.
    Local Instance pers_p1p2 (l : loc) : Persistent (p1p2 l).
    apply _. Qed.


    Definition p3 (l : loc)  (P : D) : iProp Σ :=  (saved_pred_own (encode l) (DfracOwn 1) P)%I.

    Local Instance pers_p3 (l : loc)  (P : D) : Persistent (p3 l P).
    Fail apply _.
    Abort.
   
    Definition p3' (l : loc)  (P : D) : iProp Σ :=  (saved_pred_own (encode l) (DfracDiscarded) P)%I.
    Local Instance pers_p3' (l : loc)  (P : D) : Persistent (p3' l P).
    apply _. Qed.


    (*  Global Instance saved_pred_discarded_persistent γ Φ :
            Persistent (saved_pred_own γ DfracDiscarded Φ).
        Proof. apply _. Qed. 


        do the saved predicates need to be owned ...?


        See this note on the persistent pointsto predicate from the tutorial (persistently.v)
                    (**
            Let us now turn to the `discarded' part. If one owns a fraction of a
            points-to predicate, one can decide to _discard_ the fraction. This
            means that it is no longer possible to recombine points-to predicates
            to get the full fraction. As such, the value in the points-to
            predicate can never be changed again – the location has become
            read-only. We write [l ↦□ v] for a points-to predicate whose fraction
            has been discarded. As the [□] suggests, this predicate is persistent.
            Persistent points-to predicates are great if your program has a
            read-only location, as it becomes trivial to give all threads access
            to the associated points-to predicate, and it ensures that no thread
            can sneakily update the location.

            The [pointsto_persist] lemma asserts that we can update any points-to
            predicate [l ↦{dq} v] into a persistent one [l ↦□ v].
            *)
    *)
    


    Local Instance isIt (l : loc)(P : D) : Persistent (l ↦ P).
    Proof.
        unfold Persistent.
        unfold pointsto_def.
        unfold bi_persistently.
        eexists.
        intros.


        r
        inversion  H1.
        unfold uPred_holds. simpl. red. red.

    Admitted.





   Definition D := val -> iProp Σ.

    Definition VRelType := list D -> D.

    Definition interp_TVar (v : var) : VRelType := 
        fun rho => (default (fun _ => True%I) (rho !! v)) .

    Definition interp_TUnit : VRelType := 
        fun rho v => ⌜v = UnitV⌝%I.

    Definition interp_TInt : VRelType := 
        fun rho v => (∃ (n : nat), ⌜v = IntV n⌝)%I.

    Definition interp_TBool : VRelType := 
        fun rho v => (∃ (b : bool), ⌜v = BoolV b⌝)%I.

    Definition interp_TProd (interp1 interp2 : VRelType) : VRelType := 
        fun rho v => (∃ v1 v2 , ⌜v = PairV v1 v2⌝  ∗ interp1 rho v1  ∗ interp2 rho v2)%I.

    Definition interp_TCase (interp : VRelType) : VRelType := 
        fun rho v => (∃ l, ⌜v = CaseV l⌝ ∗ l ↦ (interp rho))%I.

    Definition interp_TOSum : VRelType := 
        fun rho v => (∃ l v' P , ⌜v = InjV (CaseV l) v'⌝ ∗ l ↦ P ∗ P v')%I.

    (* what if state is modified ? *)
    Definition interp_TArrow (interp1 interp2 : VRelType) : VRelType := 
        fun rho v => (□ ∀ v', interp1 rho v' →
                        WP App (of_val v) (of_val v') {{ interp2 rho }})%I.

    (* normal forall, not fresh forall
       for fresh forall, would need to update saved predicate map? *)
    Definition interp_TForall (interp : VRelType) : VRelType := 
        fun rho v => (□ ∀ τi : D, WP TApp (of_val v) {{ interp (τi :: rho) }})%I.

    Definition interp_TExist (interp : VRelType) : VRelType := 
        fun rho v => (∃ (τi : D) v' ,  ⌜v = PackV v'⌝ ∗ interp (τi :: rho) v)%I.


    Fixpoint interp (τ : type) : list D -> D :=
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
 *)