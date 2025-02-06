From stdpp Require Import base gmap.
From Equations Require Import Equations.
From MyProject.src.OSum Require Export OSum.
From iris.base_logic Require Import upred invariants iprop.
From iris.algebra Require Import gmap ofe excl cofe_solver.


Module world.
Check fixpoint.


(* guarded type *)


Check solution.
Check prodOF.
Check ofe_morOF.
Check constOF.
Check sumOF.
Check laterOF.
Check discrete_funOF.
Check sigTOF.
(* good, components to form a poly functor out of, then take guarded fix *)


  (* define the type of streams 
    Use ID as the variable holder ..?
  *)
  
  Definition StreamF (A : ofe)`{_ : Cofe A}: oFunctor := 
    prodOF (constOF A) (laterOF idOF).

  Local Instance inhab (A : ofe)`{_ : Cofe A}`{_ : Inhabited A}  : Inhabited (oFunctor_apply (StreamF A) unitO).
  apply populate. simpl. split.
  - exact inhabitant.
  - constructor. exact ().
  Qed.

  Definition Stream_sol (A : ofe)`{_ : Cofe A}`{_ : Inhabited A} 
    : solution (StreamF A) := solver.result _.

  Definition BoolStream : ofe := Stream_sol boolO.
  Definition BoolStreamO : ofe := oFunctor_apply (StreamF boolO) (Stream_sol boolO).

  Definition unfold : BoolStream -n> BoolStreamO
    := (ofe_iso_2 (Stream_sol boolO)).

  Definition fold : BoolStreamO -n> BoolStream
    := (ofe_iso_1 (Stream_sol boolO)).
  

  Example stream : BoolStream.
    apply fold.
    constructor.
    - exact true.
    - constructor. apply fold.
      constructor.
      + exact false.
      + constructor. apply fold.
  Abort.

  Definition typeO : ofe := leibnizO type.
  Definition typeOF : oFunctor := constOF typeO.
  Definition locO := natO.

 Fail Inductive Illegal : Set := 
 | foo :(Illegal -> Illegal) -> Illegal
 | bar : () .

(* theres a coersion from (X : ofe) to constOF X *)
Definition legal : oFunctor := (▶ (idOF -n> idOF)) + unitO.

Definition legal_sol : solution (legal) := solver.result _.

Definition Legal : ofe := oFunctor_apply legal legal_sol.

Example foo : Legal := inl (Next (λne x, x)).





Lemma sndCont (A B :ofe)`{bc : Cofe} : Contractive (@snd A B).
intros.
vm_compute.
intros.
inversion x1.
unfold ofe_dist.
(* I don't see how this is true *)
Admitted.



(* 
Inductive Atom (t1 t2 : type) : Set := 
| atom : gmap loc (Atom t1 t2) -> Atom t1 t2.

Fail Fixpoint AtomP {t1 t2 : type} (a : Atom t1 t2) : Prop := 
match a with 
| (atom _ _ m) => map_Forall (fun i a => AtomP a) m
end. *)

Definition AtomF (t1 t2 : type) : oFunctor :=
    let rec : oFunctor := prodOF (prodOF typeOF typeOF) idOF in 
    let WorldF : oFunctor := 
      prodOF (
        prodOF (
          prodOF 
            stateO
            stateO
          )
          (gmapOF loc (prodOF locO locO))
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


  Definition well_typed (e : expr)(t : type)(s : state ) : Prop.
  Admitted.

  Definition state_map_typed (s : state) : Prop.
  Admitted.

  Definition rho_eta_agree : Prop.
  Admitted.

  Check (elem_of _ (dom empty)).
  Check fst.

  Definition conc (m : gmap loc (prodO locO locO)) : Prop :=
    forall (a a' : loc), a ∈ dom m -> a' ∈ dom m -> a <> a' -> 
        (fst <$> (m !! a) <> fst <$> (m !! a'))
      /\
    (snd <$> (m !! a) <> snd <$> (m !! a')).

  Check map_Forall.
  Local  Instance Atom_valid_instance (t1 t2 : type): Valid (Atom t1 t2) :=
    fun a => match a with 
      | (pair (pair e1 e2) (Next (pair (pair (pair s1 s2) eta) rho))) => 
      well_typed e1 t1 s1 /\ 
      well_typed e2 t2 s2 /\
      dom eta = dom rho /\
      conc eta /\
      state_map_typed s1 /\
      state_map_typed s2 /\
      rho_eta_agree /\
      map_Forall (fun i x => 
        match x with 
        | pair (pair t1' t2') a =>  True
        end
      ) rho
    end.
  intros x. destruct x. simpl in o. simpl in o0.
  destruct o0.
  destruct later_car.
  destruct o0.
  destruct o.
  destruct o0.



  Definition Atom_inv (t1 t2 : type) : Atom t1 t2 -n> iProp

(*   

  Simple test! and it works!
Definition AtomF (t1 t2 : type) : oFunctor :=
    let rec : oFunctor := prodOF (prodOF typeOF typeOF) idOF in 
    let WorldF : oFunctor := gmapOF loc rec in
    prodOF (prodOF exprO exprO) (laterOF WorldF).

  Local Instance inhabAtom (t1 t2 : type) : Inhabited (oFunctor_apply (AtomF t1 t2) unitO).
  Proof.
    apply populate.
    simpl.
    repeat (try constructor ; try (apply inhabitant)).
    Qed.

  Definition Atom_sol (t1 t2 : type) : solution (AtomF t1 t2) 
    := solver.result _.

  Definition Atom  (t1 t2 : type) : ofe := Atom_sol t1 t2.

  Definition AtomO (t1 t2 : type) : ofe := 
    oFunctor_apply (AtomF t1 t2) (Atom t1 t2).


  Definition Atom_fold (t1 t2 : type) : Atom t1 t2 -n> AtomO t1 t2
    := ofe_iso_2 (Atom_sol t1 t2).

  Definition Atom_unfold (t1 t2 : type) : AtomO t1 t2 -n> Atom t1 t2
    := ofe_iso_1 (Atom_sol t1 t2).
  Print prod.

  Example foo : prod bool nat.
  exact (pair true 3).
  Qed.

  Definition m : gmapO loc (prodO (prodO typeO typeO) (Atom TBool TBool)). 
  apply singletonM.
    - exact 0.
    - constructor. 
    + exact (pair TBool TBool).
    + apply Atom_unfold. 
      constructor.
      { simpl. exact (pair (Int 3) (Int 7)). }
      { simpl. apply Next. exact empty. }
    Qed.

  Example atom : Atom TBool TBool.
  Proof.
    apply Atom_unfold.
    constructor.
    -simpl. exact (pair (Bool true) (Bool false)).
    - simpl. apply Next. exact m.
  Qed.
 *)





Definition Eta : Type := gmap nat (prod nat nat).
(*
(* t1 and t2 are used in AtomT*)
Inductive AtomT (t1 t2 : type) : Type := AtomC {
  aw : WorldT _ _ ;
  ae1 : expr ; 
  ae2 : expr
}
(* t1 and t2 are used in RelT*) 
with RelT (t1 t2 : type) : Type := RelC {
  rR : AtomT t1 t2
}
with SomeRelT (t1 t2 : type) : Type := SomeRelC{
  sty1 : type ; 
  sty2 : type ;
  sR : RelT sty1 sty2
} 
with InterpT (t1 t2 : type) : Type := InterpC{
  irho : gmap nat (SomeRelT _ _ )
}
with WorldT (t1 t2 : type) : Type := WorldC{
  ws1 : state ; 
  ws2 : state ; 
  weta : Eta;
  wrho : InterpT _ _ 
}.
*)


(* t1 and t2 are used in AtomT*)
Inductive AtomT' : Type := AtomC {
  at1 : type ;
  at2 : type ;
  aw : WorldT  ;
  ae1 : expr ; 
  ae2 : expr
}
(* t1 and t2 are used in RelT*) 
with RelT' : Type := RelC {
  rt1 : type ;
  rt2 : type ;
  rR : AtomT' ;
}
with SomeRelT': Type := SomeRelC{
  sR : RelT' 
} 
with InterpT  : Type := InterpC{
  irho : gmap natO SomeRelT'
}
with WorldT : Type := WorldC{
  ws1 : state ; 
  ws2 : state ; 
  weta : Eta;
  wrho : InterpT 
}.

Example it : InterpT := InterpC empty.
Check (dom (irho it)).

(* why not have the propositions as data? *)
Inductive AtomT (t1 t2 : type) : Type := AT{
  aT : AtomT' ;
  eq_at1_t1 : at1 aT = t1 ;
  e1_at2_t2 : at2 aT = t2
}.

Arguments AT {_ _}.

Inductive RelT (t1 t2 : type) : Type := RT{
  rT : RelT' ;
  eq_rt1_t1 : rt1 rT = t1 ;
  eq_rt2_t2 : rt2 rT = t2
}.

Inductive SomeRelT : Type := ST {
  srt1 : type ;
  srt2 : type ; 
  sr : RelT srt1 srt2
}.

Definition rT'rT (rt : RelT') : RelT (rt1 rt) (rt2 rt) := 
RT (rt1 rt) (rt2 rt) rt eq_refl eq_refl.

Definition aT'aT (aT : AtomT') : AtomT (at1 aT) (at2 aT) := 
AT  aT eq_refl eq_refl.

Definition srT'srT (s : SomeRelT') : SomeRelT :=
match s with 
| SomeRelC sr => ST (rt1 sr) (rt2 sr) (rT'rT sr)
end.


Definition Conc (f : Eta) : Prop := 
forall alpha1 alpha2, 
  ((alpha1 ∈ (dom f)) 
    /\ 
  (alpha2 ∈ (dom f))
    /\
  alpha1 <> alpha2
  ) 
    -> 
    (fst <$> (f !! alpha1) <> fst <$> (f !! alpha2))
      /\
    (snd <$> (f !! alpha1) <> snd <$> (f !! alpha2))
    .

Lemma ConcEmpty :Conc empty.
Proof.
  intros a1 a2 (H1 , (H2, H3)).
  split ; eauto.
Qed. 
(*

(* atom *)
Arguments aw {_ _}.
Arguments ae1 {_ _}.
Arguments ae2 {_ _}.
(* rel *)
Arguments rR {_ _}.
(* some rel *)
Arguments sty1 {_ _}.
Arguments sty2 {_ _}.
Arguments sR {_ _}.
(* Interp *)
Arguments irho {_ _}.
(* World *)
Arguments ws1 {_ _}.
Arguments ws2 {_ _}.
Arguments weta {_ _}.
Arguments wrho {_ _}.
*)
Definition expr_store_typed (s : state)(e : expr)(t : type) : Prop:= True.

Definition store_typed (s : state) : Prop := True.

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


(* use uPred_later, not bi_later *)
Context (foo : iProp triv_sig).
Check (uPred_later foo).
Check map_Forall.

(* 
Definition map_Forall `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∀ i x, m !! i = Some x → P i x.

    Lemma big_sepM_pure_1 (φ : K → A → Prop) m :
    ([∗ map] k↦x ∈ m, ⌜φ k x⌝) ⊢@{PROP} ⌜map_Forall φ m⌝.
Definition map_Forall_bi `{Lookup K A M} (P : K → A → iProp triv_sig ) : M → iProp triv_sig  :=
  λ m, ∀ i x, m !! i = Some x → P i x.
 *)

(* This could probably be simplified ALOT, use it for now *)

Equations Atom (t1 t2 : type) : AtomT t1 t2 -> iProp triv_sig :=
Atom t1 t2 (AT (AtomC t1' t2' w e1 e2) p1 p2) := 

  (▷ (World w)) ∗ ⌜ expr_store_typed (ws1 w) e1 t1 ⌝ ∗ ⌜ expr_store_typed (ws2 w) e2 t2  ⌝

where World : WorldT -> iProp triv_sig :=
World (WorldC s1 s2 eta rho) := 
  ⌜ 
  store_typed s1 /\
  store_typed s2 /\
  dom eta = dom (irho rho) /\
  Conc eta ⌝ ∗ Interp rho

where Interp : InterpT -> iProp triv_sig  := 
Interp (InterpC sr) := ([∗ map] k↦x ∈ sr, SomeRel (srT'srT x))


where SomeRel : SomeRelT -> iProp triv_sig :=
SomeRel (ST st1 st2 sR) := Rel st1 st2 sR

where Rel (t1 t2 : type) : RelT t1 t2 -> iProp triv_sig := 
Rel rt1 rt2 (RT (RelC rt1' rt2' rR )rp1 rp2)  := Atom (at1 rR)(at2 rR) (aT'aT rR).

Check AtomC.
Check WorldC.
Example wt : WorldT := WorldC empty empty empty (InterpC empty).
Example aT' : AtomT' := AtomC TBool TBool wt (Bool true) (Bool false).
Example aaT : AtomT TBool TBool := AT aT' eq_refl eq_refl.


Example prf : ⊢@{iProp triv_sig} Atom TBool TBool aaT.
split.
intros.
unfold uPred_holds.
rewrite Atom_equation_1. 
assert (expr_store_typed (ws1 wt) (#♭ true) TBool = True) by eauto.
rewrite H1.
assert (expr_store_typed (ws2 wt) (#♭ false) TBool = True) by eauto.
rewrite H2.
simpl.
eauto.
iAssert (▷ Atom_clause_1_World TBool TBool TBool TBool wt (#♭ true) (#♭ false) eq_refl eq_refl wt).
simpl.

Search (Atom).
unfold Atom.

