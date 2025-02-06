From stdpp Require Import base gmap coPset tactics proof_irrel.

From iris.base_logic Require Import invariants iprop upred.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import cofe_solver gmap_view excl.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import Autosubst.Autosubst.

From Equations Require Import Equations.

From MyProject.src.SystemG Require Export SystemG persistent_pred.


Definition iname : namespace := nroot .@ "iname".
Check fixpoint.

Module SysGLogrel.
Import SystemG.
    Definition typeO : ofe := leibnizO type.
    Definition typeOF : oFunctor := typeO.
    Definition locO := natO.

    Definition AgreeMap (K : Type)`{_ : Countable K}`{_ : EqDecision K}(V : ofe) := gmapR K (agreeR V).

Section WorldDef.
    Context `{Σ : gFunctors}.

    (* does iProp need to be guarded here *)
    Definition Rel : ofe := prodO exprO exprO -n> iProp Σ.
    Definition SomeRel : ofe := prodO (prodO typeO typeO) Rel.

    Definition stateMap := AgreeMap loc typeO.
    Definition concMap := AgreeMap loc (prodO locO locO).
    Definition relMap := AgreeMap loc SomeRel.

    Definition World_cmra : cmra := prodR (prodR (prodR stateMap stateMap) concMap) relMap.

    (* Attempt : trying to override/extend the validity of the compositional camera
      to include the invariant on worlds. (as opposed to enforcing it with Own/Inv/World Satisfaction)  *)

    Definition World : ofe := cmra_car World_cmra.

    Definition Conc (c : concMap) : Prop. Admitted.

    Definition well_typed_stateMap (s : stateMap) : Prop. Admitted.

    Definition coherentMaps (eta : concMap) (rho : relMap): Prop. Admitted.

    Definition validSomeRel (validWorld : World -> Prop)(s : agree SomeRel) : Prop := 
    exists (w : World), validWorld  w.
(*     pose proof (elem_of_agree s).
    Admitted. *)


    Fixpoint wValidNFix (n : nat) : World -> Prop := fun w => 
    match n with 
    | O => True (* TODO *)
    | S n => 
        let s1 : stateMap := w.1.1.1 in
        let s2 : stateMap := w.1.1.2 in
        let eta : concMap := w.1.2 in 
        let rho : relMap := w.2 in 
            (* reusing the validity of the the AgreeMap structure *)
            validN (S n) s1 /\
            validN (S n) s2 /\
            validN (S n) eta /\
            validN (S n) rho /\
            (* validity of World *)
            (* state maps only hold well typed terms *)
            well_typed_stateMap s1 /\
            well_typed_stateMap s2 /\
            (* Conc: valid concretization map *)
            Conc eta /\ 
            (* Interp: valid semantic relation map *)
            map_Forall (fun k v => validSomeRel (wValidNFix n) v ) rho /\
            (* domains line up *)
            dom eta = dom rho /\
            (* partial bijection of eta and rho *)
            coherentMaps eta rho 
    end.

    (* override the existing instance (hide the other instance) 
       or just rename the type of the carrier ? *)

    Local Instance World_validN: ValidN World  := wValidNFix.
    
    Local Instance World_valid : Valid World := fun w => forall n, wValidNFix n w.


    (* using existin core should be fine *)
    Local Instance World_pcore  : PCore World . apply _. Defined.

    (* same with Op *)
    Local Instance World_op : Op World. apply _. Defined.

    (* Should be able to recyle some of the proofs from the compositional camera *)
    Lemma World_cmra_mixin : CmraMixin World.
    Proof.
    split.
    4:{ intros. eauto. }
    3:{ intros. admit. } Admitted.
    

    Canonical Structure World_cmra : cmra := Cmra World World_cmra_mixin.    
        
End WorldDef.

    Class logrelSig (Σ : gFunctors) := {
        #[local] world_res :: inG Σ (@World_cmra Σ) ;
        #[local] log_inv :: invGS Σ ;
        #[local] type_heap :: ghost_mapG Σ loc type;
        heap_name : gname ;
        world_name : gname ;
    }.

    (* TODO.. determine a proper way to map concrete program state into 
              ghost state.

              It would be nice to use WP rules to "execute" the program to a value.. 
              but we have two executions running in parallel
     *)
    Global Instance heapIG_irisG `{logrelSig Σ} : irisGS SystemG_lang Σ := {
        num_laters_per_step _ := 0;
        state_interp s  _ _ _ := ghost_map_auth heap_name 1 s;
        fork_post _ := True%I;
        state_interp_mono _ _ _ _ := fupd_intro _ _
    }.   

    Definition winv : positive := encode "winv".
    Definition winv_mask : coPset := singleton winv.
    Definition inv_name : namespace := [winv].
    

    (* bring the logic into context *)
    Context `{logrelSig Σ}.

    Definition World : ofe := cmra_car (@World_cmra Σ).

    Definition Conc_Inv (c : concMap) : iProp Σ.
    Admitted.
    
    Definition well_typed (s : stateMap)(e : expr)(t : type) : Prop.
    Admitted.

    (* Here is the tricky part.. the world invariant uses Atom and Atom uses world_inv
    need a mutual guarded fixpoint..?  
    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#fixpointAB
    *)
    Definition World_Inv (w : World) : iProp Σ :=
        match w with 
        | (((s1,s2),eta),rho) => Conc_Inv eta ∗ ⌜dom eta = dom rho⌝%I
        end.
    
    Definition Atom (t1 t2 : type) : expr -> expr -> iProp Σ :=
        fun e1 e2 => 
            (∃  (w : World), 
                ▷ (own world_name w ∗ 
                inv inv_name (World_Inv w)) ∗ 
                ⌜ well_typed (w.1.1.1) e1 t1 /\ 
                  well_typed (w.1.1.2) e2 t2 ⌝)%I.

    Definition VRelType (t : type) : Type :=  (@relMap Σ) -> ((val * val) -> iProp Σ).

    Definition interp_expr {t : type} (vr : VRelType t) : (@relMap Σ) -> ((expr * expr) -> iProp Σ) :=
        fun rho => fun p => True%I.


    (* Performs a substitution using the mapping of rho  *)
    Fixpoint concretize (t : type)(m : (@relMap Σ)) : type * type . 
    Admitted.
(*         match t with 
        | TProd t1 t2 => TProd (concretize t1 m) (concretize t2 m) 
        | TArrow t1 t2 => TArrow (concretize t1 m) (concretize t2 m) 
        | TCase l => match (m !! l) with 
                    | None => TBool
                    | Some n => TBool
                    end
        | n => n 
        end. *)

    (* checks the given types and relation against the concretization and semantic relation *)
    Definition TRel (w : World) :  (type * type * (@SomeRel Σ)) -> iProp Σ := 
        fun p => match p with 
            | ((t1,t2),r) => True%I 
        end.

    (* Here the issue with the current language definition is obvious.. 
       Autosubst is handling renaming of type variables.. our world maps are not aware of renamings *)
    Definition interp_TyVar (v : var): VRelType (TVar v). 
    Admitted.
        (*fun rho => fun p => match (p !! v) with 
                            | None => True%I
                            | Some _ => True%I
        end. *)
    
    Definition interp_TBool : VRelType TBool :=
        fun rho => fun p => Atom TBool TBool (of_val p.1) (of_val p.2).

    Definition interp_TProd {t1 t2 : type}(interp1 : VRelType t1)(interp2 : VRelType t2) : VRelType (TProd t1 t2) 
        := fun rho => fun p => 
            (∃ (v1 v2 v3 v4 : val), 
                ⌜ p.1 = (PairV v1 v2) /\ p.2 = (PairV v3 v4)⌝ ∗ 
                let c := (concretize (TProd t1 t2) rho) in 
                Atom c.1 c.2 (of_val p.1) (of_val p.2) ∗
                interp1 rho (v1 , v2) ∗ 
                interp2 rho (v3 , v4))%I.

    Definition interp_TArrow {t1 t2 : type}(interp1 : VRelType t1) (interp2 : VRelType t2) : VRelType (TArrow t1 t2) :=
        fun rho => fun p => (
            ∃ (e1 e2 : expr)(w1 w2 : World) , 
                ⌜ p.1 = (LamV e1) /\ p.2 = (LamV e2)⌝ ∗ 
                let c := (concretize (TArrow t1 t2) rho) in 
                Atom c.1 c.2 (of_val p.1) (of_val p.2) ∗
                (
                    (own world_name w1  ={ winv_mask }=∗ own world_name w2) -∗ 
                        (∀ (v1 v2 : val), 
                            interp1 rho (v1 , v2) -∗
                            interp_expr interp2 rho ((of_val(p.1)).[of_val(v1)/] ,(of_val(p.2)).[of_val(v2)/])
                        
                    )
                )
        )%I.

    Definition interp_TForall {t : type}(interp : VRelType t) : VRelType (TForall t) :=
        fun rho => fun p => 
            (∃ (e1 e2 : expr) ,
            ⌜ p.1 = (TLamV e1) /\ p.2 = (TLamV e2)⌝ ∗ 
                let c := (concretize (TForall t ) rho) in 
                Atom c.1 c.2 (of_val p.1) (of_val p.2) ∗
                ∀ (w1 w2 : World), (own world_name w1  ={ winv_mask }=∗ own world_name w2) -∗ 
                    ∀ (t1 t2 : type)(r : @SomeRel Σ), TRel w2 ((t1 , t2), r) -∗ 
                        ▷ (interp_expr interp rho (e1 , e2))
                        (* TODO, extend rho with r, perform type substitution*)
            )%I.

    Definition interp_TExist {t : type}(interp : VRelType t) : VRelType (TExist t) :=
        fun rho => fun p => 
            (∃ (v1 v2 : val) ,
            ⌜ p.1 = (PackV v1) /\ p.2 = (PackV v2)⌝ ∗ 
                let c := (concretize (TExist t ) rho) in 
                Atom c.1 c.2 (of_val p.1) (of_val p.2) ∗ 
                ∃ (w : World)(r : @SomeRel Σ) , TRel w ((TVar 0 , TVar 0), r) ∗ ▷ interp rho (v1 , v2)
                (* TODO, again.. issues with type variables. Should not be TVar 0
                  need to extend rho *)
        )%I.

    Fixpoint interp (t : type) : VRelType t :=
        match t with 
        | TBool => interp_TBool
        | TProd t1 t2 => interp_TProd (interp t1) (interp t2)
        | TArrow t1 t2 => interp_TArrow (interp t1) (interp t2)
        | TForall t => interp_TForall (interp t)
        | TExist t => interp_TExist (interp t)
        | _ => fun _ => fun _ => True%I 
        end.

    (* Testing relation definitions  *)

    Definition emptyWorld : World.
        repeat (try constructor).
    Qed.

    (* recalling "own" interpretation
    Local Program Definition uPred_ownM_def {M : ucmra} (a : M) : uPred M :=
        {| uPred_holds n x := a ≼{n} x |}.

    "iProp"
    iProp ≈ uPred (∀ i : gid, gname -fin-> (Σ i) iProp)

    "inv"
    Local Definition inv_def `{!invGS_gen hlc Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
        □ ∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
     *)
     Print own.
     Locate own.
     Check own_def.

    Check inv_alloc.
    Check own_mono.
    Lemma emptyInv (w : World ): ⊢ |==> inv inv_name (World_Inv w).
    Proof.
        iAssert (▷ (World_Inv w))%I as "D". admit.
        iApply inv_alloc.
    Lemma test : ⊢ interp TBool empty ((BoolV true) ,(BoolV false)).
    Proof.
        simpl.
        unfold interp_TBool.
        unfold Atom.
        iExists emptyWorld.
        iSplit. 2:{
            iPureIntro.
            split. { (* obviously well typed in the empty world *)
                admit. }
            admit.
         }
        iNext.
        (* this part is trickier.. 
            any interaction with inv and own need to be under a basic or fancy update modality *)
        iSplit. {
            Check inv_alloc.
            Check own_inv.
            Search (inv).
        Abort.


End SysGLogrel.
(* 

    Graveyard of other attempted definitions


    Definition EtaF : oFunctor := gmapOF loc (prodO locO locO).
    Definition AtomF : oFunctor := (typeO * typeO * exprO * exprO * ▶ ∙)%OF.
    Definition RhoF : oFunctor := gmapOF loc AtomF.
    Definition WorldF : oFunctor := (stateO * stateO * EtaF * RhoF)%OF.

    Definition World_sol : solution WorldF := solver.result _.

    Definition WorldO : ofe := World_sol.

    Definition World : ofe := 
        oFunctor_apply WorldF  WorldO .

    Definition World_fold  : WorldO  -n> World 
        := ofe_iso_2 World_sol .

    Definition World_unfold : World  -n> WorldO 
        := ofe_iso_1 World_sol .

    Definition Atom' : ofe := oFunctor_apply AtomF WorldO.

    Definition Atom (t1 t2 : type) : ofe := 
        let eqty : Atom' -> Prop := fun a => a.1.1.1.1 = t1 /\ a.1.1.1.2 = t2 in
            sigO eqty.

    Definition Eta : ofe := oFunctor_apply EtaF WorldO.
    Definition Rho : ofe := oFunctor_apply RhoF WorldO.


    (* what about worlds a later steps ? *)
    Local Instance World_dist : Dist World := fun n w1 w2 => w1 = w2.


    Local Instance World_equiv : Equiv World := equivL.

(*     Local Instance World_leib_equiv : LeibnizEquiv World.
 *)
    Canonical Structure World_ofe : ofe := (Ofe World (@discrete_ofe_mixin _ equivL eq_equivalence)).

    (* Fixing a stupid signature for now *)
    Definition triv : cmra := exclR unitO.

    Definition triv_gfun : gFunctor.
        split with (triv).
        eapply constRF_contractive.
    Defined.

    Definition triv_sig : gFunctors := gFunctors.singleton triv_gfun.

    Global Instance triv_in : inG triv_sig triv.
    Proof.
        split with (inG_id := Fin.F1); eauto. 
    Qed.

    Local Instance World_valid : Valid World.
    Admitted.

    Local Instance World_validN: ValidN World.
    Admitted.

    Local Instance World_pcore  : PCore World .
    Admitted.

    Local Instance World_op : Op World .
    Admitted.

    Lemma World_cmra_mixin : CmraMixin World .
    Admitted.
    

    Canonical Structure World_cmra : cmra := Cmra World World_cmra_mixin.

    Definition World_gFun  : gFunctor := GFunctor (constRF World_cmra).


   Program Fixpoint AtomP (a : Atom ): iProp triv_sig :=
        match a with 
        | AtomC t1' t2' e1 e2 w => (WorldP w)%I
        end
    with
    WorldP (w : World) : iProp triv_sig :=
        match w with 
        | WorldC st st2 eta rho => ([∗ map] a0 ∈ rho, AtomP a0.2)
        end.

    Equations AtomP : Atom -> iProp triv_sig :=
    AtomP (AtomC t1' t2' e1 e2 w)  := WorldP w%I

    where WorldP : World -> iProp triv_sig := 
    WorldP (WorldC st st2 eta rho) := ([∗ map] a0 ∈ rho, AtomP a0.2).

    Check fixpoint. *)
(* 

    Context (g : gmap loc loc).
    Check map_Forall _ g.
    Check big_opM bi_sep.

 Print Typing Flags.


 
    Check oFunctor_apply.
    Check discrete_funOF_apply.
Definition AtomF (t1 t2 : type) : oFunctor :=
    let rec : oFunctor := prodOF (prodOF typeO typeO) idOF in 
    let WorldF : oFunctor := 
      prodOF (
        prodOF (
          prodOF 
            stateO
            stateO
          )
          (gmapOF loc (prodO locO locO))
        )
        (gmapOF loc rec) in
    prodOF (prodOF exprO exprO) (laterOF WorldF).

  Local Instance inhabAtom (t1 t2 : type) : Inhabited (oFunctor_apply (AtomF t1 t2) unitO).
    Proof.
    apply populate.
    simpl.
    repeat (try constructor ; try (apply inhabitant)).
    Qed.

  Definition Atom_sol (t1 t2 : type) : solution (AtomF t1 t2) 
    := solver.result _.


  Definition AtomO  (t1 t2 : type) : ofe := Atom_sol t1 t2.

  Definition Atom (t1 t2 : type) : ofe := 
    oFunctor_apply (AtomF t1 t2) (AtomO t1 t2).

  Definition Atom_fold (t1 t2 : type) : AtomO t1 t2 -n> Atom t1 t2
    := ofe_iso_2 (Atom_sol t1 t2).

  Definition Atom_unfold (t1 t2 : type) : Atom t1 t2 -n> AtomO t1 t2
    := ofe_iso_1 (Atom_sol t1 t2).




(* 
    Definition eta : oFunctor := gmapOF loc (prodO locO locO).
    Definition P : (prodO typeO typeO → oFunctor) := fun _ => (exprO * exprO * ▶ ∙)%OF.

    Definition AtomF : oFunctor := {x : prodO typeO typeO & P x}%OF.
    Definition rho : oFunctor := gmapOF loc AtomF.
    Definition WorldF : oFunctor := (stateO * stateO * eta * rho)%OF. *)


    Definition eta : oFunctor := gmapOF loc (prodO locO locO).
    Definition P : (prodO typeO typeO → oFunctor) := fun _ => (exprO * exprO * ▶ ∙)%OF.
    Definition AtomF : oFunctor := {x : prodO typeO typeO & P x}%OF.
    Definition rho : oFunctor := gmapOF loc AtomF.
    Definition WorldF : oFunctor := (stateO * stateO * eta * rho)%OF.


    Local Instance dec_type (a b : type) : Decision (a = b).
    Admitted.
    Local Instance dec_pair_type (a b : type * type) : Decision (a = b).
    Admitted.

    Local Instance pi_pair_type : ∀ a b : type * type, ProofIrrel (a = b).
    intros.
    eapply eq_pi.
    apply _.
    Qed.

    Definition World_sol : solution WorldF := solver.result _.

    Definition WorldO : ofe := World_sol.

    Definition World : ofe := 
        oFunctor_apply WorldF  WorldO .

    Definition World_fold  : WorldO  -n> World 
        := ofe_iso_2 World_sol .

    Definition World_unfold : World  -n> WorldO 
        := ofe_iso_1 World_sol .

    Example world : World  := pair (pair (pair empty empty) empty) empty.

    Check AtomF.
    Definition Atom (t1 t2 : type) : oFunctor := P (pair t1 t2).

    Example atom : Atom TBool TBool.

 Print Typing Flags.
    Unset Universe Checking.
    Print Typing Flags.

    Definition AtomWorld (t1 t2 : type) : prod oFunctor oFunctor :=
        let rec : oFunctor := prodOF (prodOF typeO typeO) idOF in 
        let WorldF : oFunctor := 
        prodOF (
            prodOF (
            prodOF 
                stateO
                stateO
            )
            (gmapOF loc (prodO locO locO))
            )
            (gmapOF loc rec) in
        pair (prodOF (prodOF exprO exprO) (laterOF WorldF)) WorldF.

    Print Typing Flags.


    Definition AtomF (t1 t2 : type) : oFunctor := (AtomWorld t1 t2).1.
    Set Universe Checking.

 
    (* universe flag nonsense so I can return multiple oFunctors *)
   (*  Unset Universe Checking.
    Print Typing Flags.

    Definition TYPES : oFunctor * (oFunctor * oFunctor) := 
        let Atom : oFunctor := {x : prodO typeO typeO & P x}%OF  in
        let rho : oFunctor := gmapOF loc Atom in
        let World : oFunctor := (stateO * stateO * eta * rho)%OF in 
        pair Atom (pair rho World).

    Definition AtomF : oFunctor := TYPES.1.
    Definition RhoF : oFunctor := TYPES.2.1.
    Definition WorldF : oFunctor := TYPES.2.2.

    Set Universe Checking.
    Print Typing Flags. *)

    *)