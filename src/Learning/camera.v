
(* Here are the basic algebras we can use 
https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra

some base types
and type constructors on Ofes
includin Pi types and Sigma types
https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#boolO
*)

From Equations Require Import Equations.

From stdpp Require Import list gmap fin_maps.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset excl.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import options.
From stdpp Require Import base  gmap.
From stdpp Require Export countable infinite fin_maps fin_map_dom.
From stdpp Require Import mapset pmap.
From stdpp Require Import options.
From iris.prelude Require Import options.



From iris.algebra Require Import ofe gmap.
From iris.base_logic Require Import gen_heap invariants.

From iris.proofmode Require Import proofmode.

From MyProject.src.OSum Require Export OSum.


Inductive myResource := Start | Finish | Invalid.
Check eq.
(* defining a resource algebra on for this type.
we can make an ofe from the discrete_ofe_mixin
 *)
Print discrete_ofe_mixin.
(*this relys on our type having typeclass instances for 
    Equiv
    and 
    Equivalence
*)
Print Equiv. (* this is just a binary relation on A *)
Print relation.
(* equiv is the field for this type class*)
Print equiv.

(* we also need to show that relation specified by the Equiv instance
is actually an equivalence relation (relf, sym, trans)*)
Print Equivalence.


(* just use (propositional) equality for the relation *)
Global Instance state_equiv_instance : Equiv myResource := eq.

(* equality is obviously an equivalence relation *)
Check @equiv myResource.
(* this summons the type class instance *)
Check (≡@{myResource}).
Global Instance state_equiv_equivalence : Equivalence (≡@{myResource}).
Proof.
    constructor.
    (* reflexive *)
    - Print Reflexive. exact reflexivity.
    (* sym *)
    - Print Symmetric. exact symmetry.
    (* trans *)
    - Print Transitive. exact transitivity. 
Qed.

(**
  To help convert between equivalence and equality, we can tell Iris
  that they coincide, which in this case is trivial.
*)
Global Instance myResource_leibniz_equiv : LeibnizEquiv myResource := _.

Canonical myOfe := Ofe myResource (discrete_ofe_mixin _).

(* now we have an Ofe .. lets define an PCM on that OFE 
aka a resource algebra *)

Fail Lemma myResource_ra_mixin : RAMixin myResource.

(* for this, we need instances of PCore, Op, and Valid*)


Print PCore.
(* 
From the tutorial

  Finally, the core, written [pcore x] for a resource [x], is a partial
  function which extracts exactly the _shareable_ part of a resource. We
  handle partiality in Coq by letting the core return an option. We
  write [pcore x = Some y] to mean that the shareable part of resource
  [x] is [y]. Similarly, we write [pcore x = None] to mean that [x] has
  no shareable part. For resources [x] that are entirely shareable, we
  have that [pcore x = Some x].

 For this resource, make Start exclusive and the other constructors sharable
*)
Global Instance myResource_pcore : PCore myResource := 
    fun x => match x with 
            | Start => None 
            | Finish => Some x 
            | Invalid => Some x
            end. 

(* the operations on the resource 
Tutorial:
Thirdly, the operation, written [x ⋅ y] for resources [x, y ∈ A],
  shows us how to combine resources.
*)
Print Op.
(* idk why this operation is chosen, following tutorial*)
Local Instance myResource_op_instance : Op myResource := λ s1 s2,
  match s1, s2 with
  | Finish, Finish => Finish
  | _, _ => Invalid
  end.

(*lastly, we need an instance of Valid
tutorial: 
  Fourthly, we distinguish between valid and invalid resources, writing
  [✓ x] to denote that [x] is valid. Intuitively, validity captures that
  the combination of some resources should not be allowed. In the logic,
  if we combine two valid resources and their combination is invalid,
  then we will be able to derive falsehood.
*)
Print Valid.
Local Instance myResource_valid_instance : Valid myResource := λ s,
  match s with
  | Start | Finish => True
  | Invalid => False
  end.

(* now the type classes for Op, PCore, and Valid are in scope
we can prove these make a resource algebra *)
Lemma myResource_ra_mixin : RAMixin myResource.
Proof.
    constructor.
    - Print Proper. (*Proper type classes ? *)solve_proper.
    - intros. exists cx. split. * rewrite <- H. exact H0. * reflexivity.
    - (* proper again ..?*) solve_proper.
    - (* associativity of the operation*)
        intros [] [] [] ; eauto. (* brute force, compute all possibilities*)
    - (* commutative *) 
    intros [] [] ; eauto.
    - (* core id *) by intros [] [].
    - (* core idem *) by intros [] [].
    - (* core mono *) intros [] _ [] [[] ->] e; try done.
    all: eexists; split; first done.
    all: try by exists Invalid.
    by exists Finish.
    - (* valid op*) by intros [] [].
    (* order is extension order *)
Qed.

(* now we have a camera *)
Canonical Structure myResourceR := discreteR myResource myResource_ra_mixin.

Global Instance state_cmra_discrete : CmraDiscrete myResource.
Proof. Check discrete_cmra_discrete. apply discrete_cmra_discrete. Qed.

(**
  To alleviate working with the State RA, we here show some useful facts
  about the resource algebra. Firstly, [Start] is exclusive and [Finish]
  is shareable.
*)

Print Exclusive.
Print CoreId.
Global Instance Start_exclusive : Exclusive Start.
Proof. by intros []. Qed.

Global Instance Final_core_id : CoreId Finish.
Proof. red. done. Qed.

(* Starting here, it is best to follow section 2 of 
    Iris From the Ground UP

*)
(* logical connectives related to resources *)

(* deterministic and non-determinnistic updates to resouces
    "frame preserving updates"
*)

(* this is syntax for deterministic update and non-deterministic update*)
Print cmra_update. (*deterministic *)
Print cmra_updateP. (* non deterministic *)
Lemma myupdate s : s ~~> Finish.
Proof.
    red.
    (* this translates to 
    ∀ (n : nat) (mz : option myResourceR), 
        ✓{n} (s ⋅? mz) → ✓{n} (Finish ⋅? mz)


    the step indexing doesn't matter here since our camera is discrete
    *)
    apply cmra_discrete_update.
    (* ∀ mz : option myResourceR, ✓ (s ⋅? mz) → ✓ (Finish ⋅? mz) 
    
    Note that the operation  .? is 

        Definition opM `{!Op A} (x : A) (my : option A) :=
        match my with Some y ⇒ x ⋅ y | None ⇒ x end.
        Infix "⋅?" := opM (at level 50, left associativity) : stdpp_scope.
    
    *)
    intros mz H.
    (* now this proceeds as a basic case analysis*)
    destruct mz ; destruct s ; compute in H ; try (exact H) ; 
    try (exfalso ; exact H).
Qed.

(* how to create a resource

    view shifts?
        defined in terms of basic and fancy updates?

    These are stated in terms of "basic" and "fancy" updates ?
    https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/updates.v?ref_type=heads#L16


    Library for invariants?
    https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.invariants.html#inv_contractive

 *)
Check own.
Fail Lemma alloc_Start : ⊢ |==> ∃ γ, own γ Start.

(* in order for this proposition to make sense,
we need to fix a logic, and to do that
we need to chose a resource*)


(* getting gFUnctors from a single camera *)
Definition rfun : rFunctor := constRF  myResourceR.
Definition rfuncont : rFunctorContractive rfun.
  eapply constRF_contractive.
Defined.

Definition gfun : gFunctor := {|
gFunctor_F := constRF  myResourceR ;
gFunctor_map_contractive := rfuncont
|}.

Definition myResourceFun : gFunctors := gFunctors.singleton gfun.

(* now we can talk about propositions in a logic 
with our notion of resource*)

(* ⊢ is notation for bi_entails*)
Check bi_entails.

Lemma myFirstLemma : ⊢@{iProp myResourceFun} (True%I).
Proof.
    eauto.
Qed.


(* we need a typeclass proof that MyResourceR is in the gFunctor MyResourceFun *)
Fail Lemma fail : ⊢@{iProp myResourceFun} |==> ∃ γ, own γ Start. 
(* Could not find an instance for "inG myResourceFun myResourceR" in environment:
γ : gname*)

Global Instance myResourceIn : inG myResourceFun myResourceR.
Proof.
    split with (inG_id := Fin.F1); eauto.
Qed.

Lemma allocRes : ⊢@{iProp myResourceFun} |==> ∃ (γ : gname), own γ Start.
Proof.
    Print gname.
    Print own.
    Check own_alloc.
    iApply own_alloc. 
    (* only valid resources can be allocated, show Start is valid *)
    red. red. red. red. auto.
Qed.

(* Since only valid things can be alloced, 
if own a resource then it must be valid *)

Lemma is_valid γ (s : myResource) : own γ s ⊢ ⌜✓ s⌝.
Proof.
  iIntros "H".
  Check own_valid.
  iPoseProof (own_valid with "H") as "%H".
  done.
Qed.


(* valid updates in the resource algebra can be "lifted" 
to ownership predicates
  shorthand for [_ -∗ |==> _] is [_ ==∗ _].
 *)

Lemma my_bupd γ (s : myResource) : own γ s ==∗ own γ Finish.
Proof.
Check own_update.
  iApply own_update.
  apply myupdate.
Qed.




(* more complicated resources *)
Check authUR.
Check agreeR.
Check gmapUR.
Print gmapUR.

(* consider a map from Nat to Bool as a resource *)
Print natO.
Print boolO.

(* bool agree camera*)
Definition AgreeBool : cmra := agreeR boolO.

Definition AgBool_op : agree bool -> agree bool -> agree bool 
:= @op _ (cmra_op AgreeBool).

Eval compute in AgBool_op  (to_agree true) (to_agree false).

Definition AgBool_valid : agree bool -> Prop 
:= @valid _ (cmra_valid AgreeBool).

Eval compute in agreeR boolO.
Eval compute in AgBool_valid (to_agree true).
Eval compute in AgBool_valid (to_agree false).
Eval compute in AgBool_valid (AgBool_op (to_agree true) (to_agree true)).
Eval compute in AgBool_valid (AgBool_op (to_agree false) (to_agree true)).

Lemma allValid (b : bool) : AgBool_valid (to_agree b).
Proof.
    destruct b ; compute ; eauto. 
Qed.

(* you can derive false if a combination of valid elements is not valid*)
Lemma cantCombineNotEqual (b1 b2 : bool) : b1 <> b2 -> 
    AgBool_valid (AgBool_op (to_agree b1) (to_agree b2)) -> 
    False.
Proof.
    intros.
    destruct b1 ,b2.
    - compute in H. eauto.
    - compute in H0.
        assert (true = false). 
        + apply H0.
        * exact 0.
        * constructor.
        * constructor. constructor.
        + contradiction.
    - compute in H0. 
                assert (true = false). 
        + apply H0.
        * exact 0.
        * constructor. constructor.
        * constructor.
        + symmetry in H1. contradiction.
    - compute in H. eauto.
Qed.

(* this should be false ...
not provable
*)
Lemma dadf : (to_agree true) ~~> (to_agree false).
Proof.
    red.
    apply cmra_discrete_update.
    intros.
    induction mz.
    - induction a.
        * induction agree_car.
         + compute in agree_not_nil . inversion agree_not_nil.
         + simpl. 
         Admitted.

(* agree camera*)
Definition ab : cmra := agreeR boolO.
(* summon the typeclass instances *)
Definition ab_op : ab -> ab -> ab := op.
Definition ab_core : ab -> option ab := pcore.
Definition ab_valid : ab -> Prop := valid.

(* definition
Given (c : cmra)
The carier is a "list (carrier c)" that is supposed to represent a finite set of "carier c"
    this is then quotiented by a relation to ensure that any lists that contain the 
    same elements are considered equal subsets of  "carrier c"

"combining subsets of the carrier c is set union (encoded here as appending lists)"
Local Program Instance agree_op_instance : Op (agree A) := λ x y,
  {| agree_car := agree_car x ++ agree_car y |}.

"The core is always defined"
Local Instance agree_pcore_instance : PCore (agree A) := Some.

"Validity at a timestep n"
"if,  the set is a singleton, then it is valid
else, any two elements of the subset of carrier c must be considered equal at timestep n"
Local Instance agree_validN_instance : ValidN (agree A) := λ n x,
  match agree_car x with
  | [a] ⇒ True
  | _ ⇒ ∀ a b, a ∈ agree_car x → b ∈ agree_car x → a ≡{n}≡ b
  end.

"validity is of a subset X of carrier c is true IF
    forall timesteps n, any two elements of subset X are equal at step n "

"note that if agree is over a discrete camera or discrete ofe, 
then the agree camera is just partitions the carrier of the original resource by equality"
Local Instance agree_valid_instance : Valid (agree A) := λ x, ∀ n, ✓{n} x.
*)

(* for an example, consider the discrete ofe natO*)
Print natO.
Definition anat : cmra := agreeR natO.

(* for our discrete nat camera, an element of anat is just a non empty subset of nat 
presented as a list*)

Example anatelem : anat.
esplit with ([1 ; (0 + 1) ; (1 + 0)]).
compute ; reflexivity.
Defined.

(* since all elements of this subset of nat are equal, then this is a valid element of agree nat*)
Lemma validlist : valid anatelem .
Proof.
    compute.
    intros.
    assert (a = 1).
    - inversion H ; eauto. inversion H3 ; eauto. inversion H7 ; eauto. inversion H11.
    - assert (b = 1).
    +inversion H0 ; eauto. inversion H4 ; eauto. inversion H8 ; eauto. inversion H12.
    + rewrite H1. rewrite H2. reflexivity.
Qed.

(* however, this is not a valid element of antat*)
Example invalid : anat.
esplit with ([1 ; 2]).
compute ; reflexivity.
Defined.

Lemma notvalid : valid invalid -> False.
Proof.
    compute.
    intros.
    assert (1 = 2).
    - apply H.
        + exact 0.
        + constructor.
        + constructor. constructor.
    - inversion H0.
Qed.

(* the to_argree constructor makes a singleton set*)
Example sn (n : nat) : anat.
split with ([n]).
compute ; reflexivity.
Defined.
Example sing (n : nat) : to_agree n = sn n.
compute. reflexivity.
Qed.

(* singleton sets should always be valid *)
Lemma to_agree_valid {A : cmra}{x : A} : valid (to_agree x).
compute. eauto.
Qed.


(* 1 + 1 and 2 are equal elements of nat, independent of timestep
therefore we should be able to combine them and the result should be valid*)
Example eqnat : ✓ (to_agree (1 + 1) ⋅ to_agree 2).
rewrite to_agree_op_valid.
reflexivity.
Qed.

(* but this should be false *)
Example neqnat :  ✓ (to_agree 1 ⋅ to_agree 2) -> False.
intros.
rewrite to_agree_op_valid in H.
inversion H.
Qed.

(* the core is always defined *)
Example corealwaysdef : ab_core = Some.
reflexivity.
Qed.

(* updates are not that interesting *)
Lemma equpdate (n m : nat): n = m -> (to_agree n) ~~> (to_agree m).
Proof.
    intros.
    apply cmra_discrete_update.
    intros. rewrite <- H. exact H0.
Qed.

Lemma nequpdate (n m : nat) : n <> m -> ((to_agree n ~~> to_agree m) -> False).
Proof.
    intros.
    rewrite cmra_discrete_update in H0.
    pose proof (H0 (Some (to_agree n))).
    simpl in H1.
    assert (✓ (to_agree n ⋅ to_agree n)).
    - rewrite to_agree_op_valid. reflexivity.
    - pose proof (H1 H2).
    pose proof (H3 0 n m).
    assert (n ∈ agree_car (to_agree m ⋅ to_agree n)) ; try( repeat constructor).
    assert (m ∈ agree_car (to_agree m ⋅ to_agree n)) ; try (repeat constructor).
    pose proof (H4 H5 H6).
    contradiction.
Qed.


(* important properties
Lemma to_agree_op_valid a b : ✓ (to_agree a ⋅ to_agree b) ↔ a ≡ b.

Lemma to_agree_uninj x : ✓ x → ∃ a, to_agree a ≡ x.

*)

(* allocating elements *)

Definition anat_gfun : gFunctor.
split with (constRF anat).
eapply constRF_contractive.
Defined.

Definition anat_sig : gFunctors := gFunctors.singleton anat_gfun.

Global Instance anat_in : inG anat_sig anat.
Proof.
    split with (inG_id := Fin.F1); eauto.
Qed.

(* any valid anat can be allocated *)
Lemma allocanat (an : anat):
    valid an -> 
     ⊢@{iProp anat_sig} |==> ∃ (γ : gname), own γ an.
Proof.
    intros.
    iApply own_alloc. 
    exact H.
Qed. 



(* exclusive camera *)
Print exclR.
(* the carrier is basically an option type over some OFE*)
Print excl.

Definition enat := exclR (natO).

(* summon typeclass instances *)
Definition enat_op : enat -> enat -> enat := op. 
Definition enat_valid : enat -> Prop := valid.
Definition enat_core : enat -> option enat := pcore.

(* definitions 
carrier
    Inductive excl (A : Type) :=
    | Excl : A → excl A
    | ExclBot : excl A.

op
    Local Instance excl_op_instance : Op (excl A) := λ x y, ExclBot.

valid 
    Local Instance excl_valid_instance : Valid (excl A) := λ x,
        match x with Excl _ ⇒ True | ExclBot ⇒ False end.

validN
    Local Instance excl_validN_instance : ValidN (excl A) := λ n x,
        match x with Excl _ ⇒ True | ExclBot ⇒ False end.

core 
    Local Instance excl_pcore_instance : PCore (excl A) := λ _, None.

*)

(* constructing enats*)
Example en1 : enat := Excl 7. (* some *)
Example en2 : enat := ExclBot. (* none *)

(* validity is essentiatly a "inhabited : option A -> Prop" 
    it is True in the Some case
    it is False in the None case
*)

Lemma yesenat : valid en1.
compute.
auto.
Qed.

Lemma nonat : valid en2 -> False.
intros.
compute in H.
exact H.
Qed.

(* the core is ALWAYS None *)
Lemma emptycore (en : enat) : pcore en = None.
compute. reflexivity.
Qed.

(* combining any two elements is always None/False/ExclBot*)
Lemma nocombos (n1 n2 : enat) : op n1 n2 = ExclBot.
compute. reflexivity.
Qed.

(* therefore it is never valid to combine elements *)
Lemma opnevervalid (n1 n2 : enat) : valid (op n1 n2) = False.
compute. reflexivity.
Qed.


(* option camera *)
Print optionR.

Definition o_op {A : cmra} : option A -> option A -> option A := op.
Definition o_valid {A : cmra} : option A -> Prop := valid.
Definition o_pcore {A : cmra} : option A -> option (option A) := pcore.
(* 
Definitions 
    Local Instance option_op_instance : Op (option A) :=
        union_with (λ a b, Some (a ⋅ b)).

    Local Instance option_valid_instance : Valid (option A) := λ ma,
        match ma with Some a ⇒ ✓ a | None ⇒ True end.

    Local Instance option_pcore_instance : PCore (option A) := λ ma,
        Some (ma ≫= pcore).
*)
Example op1 {A : cmra} : @o_op A None None = None.
reflexivity. Defined.

Example op2 {A : cmra}{x : A} : o_op (Some x) None = Some x.
reflexivity. Defined.

Example op3 {A : cmra}{x : A} : o_op None (Some x) = Some x.
reflexivity. Defined.

Example op4 {A : cmra}{x y : A} : o_op (Some x) (Some y) = Some (op x y).
reflexivity. Defined.

(* finite map camera *)
Check gmapR.
(* 
Local Instance gmap_unit_instance : Unit (gmap K A) := (∅ : gmap K A).
Local Instance gmap_op_instance : Op (gmap K A) := merge op.
Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Local Instance gmap_validN_instance : ValidN (gmap K A) := λ n m, ∀ i, ✓{n} (m !! i).

breaking down op
    merge op
    merge is an operation 
        merge
            : (option ?A → option ?B → option ?C) → ?M ?A → ?M ?B → ?M ?C
        where
        ?M : [ |- Type → Type]
        ?Merge : [ |- Merge ?M]
        ?A : [ |- Type]
        ?B : [ |- Type]
        ?C : [ |- Type]

    and op here is actually op from the Option Camera!
    which is the union
    None , None => None
    Some x , None => Some x 
    None , Some y => Some y 
    Some x , Some y => Some (op x y)

    thus, when maps have overlapping values
        k |-> v1 
        k |-> v2 
    combining these maps results in 
    k |-> op v1 v2

*)
Check merge.
Print gmap_merge.




Definition bmap : cmra := gmapR nat ab.


(* summon the typeclass instances *)

Definition bm_op : bmap → bmap → bmap := op.
Definition bm_core : bmap -> option bmap := pcore.
Definition bm_valid : bmap -> Prop := valid.

(* using bmap here causes issues with tyring to infer M in map_eq *)
Example m1 : gmap nat (agreeR boolO) := {[ 0 := (to_agree true) ]}.

Example m2 : gmap nat (agreeR boolO) := {[ 1 := (to_agree false) ]}.

Example m3 : gmap nat (agreeR boolO) := list_to_map [(0 , to_agree true); (1 , to_agree false)].

Lemma mapneq  : m1 <> m2.
Proof.
    red.
    intros. inversion H.
Qed.

Lemma mapeq : m1 = m1.
    apply map_eq.
    intros i.
    destruct i.
    - simplify_map_eq. reflexivity.
    - eauto.
Qed.

Lemma m3eq : op m1 m2 = m3.
Proof.
    apply map_eq.
    intros i.
    eauto.
Qed.

Check lookup.
(* what about if map has conflicting domain?*)
Example m1' : bmap := {[ 0 := (to_agree false) ]}.

(* it looks like that, in the case of a conflict,
    you use the Values op 
    That makes sense why we'd like and Agree camera on the Value*)
Example what : (op m1 m1') !! 0 = Some (to_agree true ⋅ to_agree false).
simplify_map_eq.
reflexivity.
Qed.

Check omap.
(* what is the core of a map ?
Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
    where 
        omap
            : (?A → option ?B) → ?M ?A → ?M ?B
        where
        ?M : [ |- Type → Type]
        ?OMap : [ |- OMap ?M]
        ?A : [ |- Type]
        ?B : [ |- Type]

so pcore on maps just maps pcore on the Values

*)
Example mcore : pcore m1 = Some m1.
Proof.
    vm_compute.
reflexivity.
Qed.

Example gs : gset nat.
constructor.
exact {[ 0 := () ]}.
Defined.

Example m1d : dom m1 = gs.
set_solver.
Qed.

Example hmm (i : nat) : i <> 0 -> m1 !! i = None.
Proof.
    intros. 
    assert (m1 !! i = None) by (apply not_elem_of_dom; set_solver).
    exact H0.
Qed.

(* validity is pointwise

    Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).

    so combining these maps should be valid  
        Example m1 : gmap nat (agreeR boolO) := {[ 0 := (to_agree true) ]}.

        Example m2 : gmap nat (agreeR boolO) := {[ 1 := (to_agree false) ]}.
 *)


Example vm : valid (op m1 m2).
Proof.
    rewrite m3eq.
    red. red. red. red.
    intros i.
    (* lets do by cases*)
    destruct i.
    - (* 0 evaluates to Some (to_agree true)*) simplify_map_eq. 
     (* what is the validity of option ..?
    
        None => True
        Some x => valid x
     *)
     rewrite Some_valid.
     (* any singleton in agree is valid*)
    compute; eauto.
    - destruct i.
    + simplify_map_eq.
    rewrite Some_valid ; compute; eauto.
    + (* how to show the map is no longer defined ..?*)
     assert (m3 !! (S (S i)) = None) by ( apply not_elem_of_dom ; set_solver).
     rewrite H.
     constructor.
    Qed.
     
(* however, combining m1 and m1; is invalid 
because they point to conflicting elements at index 0*)
Example invm : valid (op m1 m1') -> False.
Proof.
    intros.
    assert (op m1 m1' = {[ 0 := op (to_agree true)(to_agree false)]}) by eauto.
    rewrite H0 in H.
    (* we know they disagree at index 0*)
    pose proof (H 0 0 true false) as H.
    assert (true ∈ agree_car (to_agree true ⋅ to_agree false)) by repeat constructor.
    assert (false ∈ agree_car (to_agree true ⋅ to_agree false)) by repeat constructor.
    pose proof (H H1 H2).
    inversion H3.
Qed.

(* transitions between these resources will be interesting ..*)
Print m3.
Lemma trythis : m1 ~~> m3.
Proof.
    apply cmra_discrete_update.
    (* if any arbitrary map can be combined with m1...
    then any arbitrary map can be combined with m3 ..?
    
    That doesn't seem right
        for example, m1 can be combined with 1 -> true 
        but m3 cannot , it would conflict...
    *)
Abort.

Print m1.
(* however, the reference manual states the following are true*)
Definition bempty : bmap := empty.

Lemma bempty_valid : valid bempty.
Proof.
    intros i.
    rewrite lookup_empty.
    done.
Qed.

Lemma fpfn_alloc (b : agreeR boolO)(vm : valid b)(i : nat) : bempty ~~> {[ i := b ]}.
Proof.
    apply cmra_discrete_update.
    intros.
    destruct mz.
    2:{
    (* the easy case, if "mz = None" *)
    simpl. 
    (* a singleton map should be valid if the only element is valid *)
    rewrite singleton_valid ; exact vm.
    }
    (* the Some case *)
    simplify_map_eq. 
     apply cmra_valid_op_r in H.
    eassert (valid {[i := b]}). 1:{ 
        apply singleton_valid ; exact vm.
    }
    (*we have that the individual maps are valid.. 
        but we have to show their merge is valid

            Search (✓ (?x ⋅ ?y)).

    pointwise
     *)
     intros j.
     pose proof (H j).
     (* distribute the index to both maps*)
     rewrite lookup_op.

    (* we don't know what will happen with c !! j.. but we at least know ..*)
    assert (c !! j = None \/ exists x , (c !! j = Some x /\ (valid (Some x) -> valid x))). {
        destruct (c !! j).
        - right. exists c0. split ; try (reflexivity). intros. rewrite  Some_valid in H2. exact H2.
        - left ; reflexivity.
    }
    destruct (decide (i = j)).
    1:{
        rewrite e. 
        rewrite lookup_partial_alter.
        destruct H2. {
            rewrite H2.
            intros k. exact (vm k).
        }{
          destruct H2.
          destruct H2.
          rewrite H2. 
          intros k.  
            (* we dont know that b and c !! j agree!*)
        Abort.

Lemma fpfn_allocFalse (i : nat) : (bempty ~~> {[ i := (to_agree true) ]}) -> False.
Admitted.
(*  apply with mz = Some ({[i := to_agree true]})) *)
(* create a conflict *)

(* Heres the lemma I was trying to prove *)
(* See https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.gmap.html#properties.freshness *)
Check alloc_unit_singleton_update.

Example attempt : ∅ ~~> {[0 := to_agree true]}.
eapply alloc_unit_singleton_update with (u := (to_agree true)).
- apply @to_agree_valid with (A := ab ) (x := to_agree true).
- red. intros. (* cant prove to_agree true ⋅ x ≡ x *) Abort.


(* next, look into the "Auth or View" camera 

    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.auth.html#auth

    Definition authR (A : ucmra) : cmra := viewR (A:=A) (B:=A) auth_view_rel.

    where 
        Record view {A B} (rel : nat → A → B → Prop) :=
            View { view_auth_proj : option (dfrac × agree A) ; view_frag_proj : B }.

    Canonical Structure auth_view_rel {A : ucmra} : view_rel A A :=
    ViewRel auth_view_rel_raw (auth_view_rel_raw_mono A)
            (auth_view_rel_raw_valid A) (auth_view_rel_raw_unit A).

and the specific instance for gmap

    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.lib.gmap_view.html#gmap_viewR

    Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra :=
        viewR (gmap_view_rel K V).

    Local Canonical Structure gmap_view_rel : view_rel (gmapO K V) (gmap_view_fragUR K V) :=
    ViewRel gmap_view_rel_raw gmap_view_rel_raw_mono
            gmap_view_rel_raw_valid gmap_view_rel_raw_unit.

    where 
        Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
            gmapUR K (prodR dfracR V).


A Ghost Map is
    Class ghost_mapG Σ (K V : Type) `{Countable K} := GhostMapG {
     #[local] ghost_map_inG :: inG Σ (gmap_viewR K (agreeR (leibnizO V)));
    }.

    Ghost maps already have a points to connective
        Notation "k ↪[ γ ] dq v" := (ghost_map_elem γ k dq v)

    where 
          Local Definition ghost_map_elem_def
            (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
            own γ (gmap_view_frag (V:=agreeR $ leibnizO V) k dq (to_agree v)).

    a "Heap" provides an extra nicety where we don't need the ghost name in the points to connective

    "For HEAP"
        Local Notation "l ↦ dq v" := (pointsto l dq v)
        
        where
              Local Definition pointsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
                l ↪[gen_heap_name hG]{dq} v.

And a heap with a points to connectie is 
    A ghost_map L V, which keeps track of the values of locations.

    A ghost_map L gname, which keeps track of the meta information of locations. 
        More specifically, this RA introduces an indirection: 
        it keeps track of a ghost name for each location.
    
    The ghost names in the aforementioned authoritative RA refer to namespace maps 
        reservation_map (agree positive), which store the actual meta information. 
        This indirection is needed because we cannot perform frame preserving updates 
        in an authoritative fragment without owning the full authoritative element 
        (in other words, without the indirection meta_set would need gen_heap_interp as a premise).

heap interpretation


    Definition gen_heap_interp (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,
        
        ⌜ dom m ⊆ dom σ ⌝ ∗
        ghost_map_auth (gen_heap_name hG) 1 σ ∗
        ghost_map_auth (gen_meta_name hG) 1 m.

    where

        Local Definition ghost_map_auth_def
            (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
            own γ (gmap_view_auth (V:=agreeR $ leibnizO V) (DfracOwn q) (to_agree <$> m)).

    and
          Definition gmap_view_auth (dq : dfrac) (m : gmap K V) : gmap_viewR K V :=
            ●V{dq} m.


    so 
        Definition gen_heap_interp (σ : gmap L V) : iProp Σ := 
            ∃ m : gmap L gname,
                ⌜ dom m ⊆ dom σ ⌝ ∗
                own (gen_heap_name hG) (●V{1} σ) *
                own (gen_meta_name hG) (●V{1} m)
*)

(* recursive predicates*)

Check fixpoint.
Print fixpoint.
(* use a trivial resource for these examples *)

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

Print nat.
Locate fixpoint.

(* morphism in the category OFE *)
Check (natO -d> natO).

Definition add' (rec : prodO natO natO -d> natO) : prodO natO natO -d> natO := 
fun p => 
    match p with 
    | (O , m) => m 
    | (S n , m) => S (rec (n , m))
    end.

Fail Program Definition add : prodO natO natO -d> natO  := fixpoint add'.

Print respectful.
Print proper_prf.
(* need to prove Contractive add' 

    f : A -> A is contractive if 
    
    forall (n : nat)(x y : A), 
            (forall (m : nat), m < n -> x ={m} y)
        ->
            (f x ={n} f y)

    
    Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).


*)
Global Instance add'_contractive : Contractive add'.
Proof.
    try f_contractive.
    try solve_contractive.
    try solve_proper.
    intros.
    try solve_proper.
    red. red. intros.
    destruct H.
    Admitted.
Program Definition add : prodO natO natO -d> natO  := fixpoint add'.

Eval vm_compute in (add (1 , 2)).


Definition myRec (p : natO -d> iProp triv_sig) : natO -d> iProp triv_sig :=
 fun n => match n with 
        | O => True%I
        | S n => bi_later (p n) 
 end.

Check bi_later.
Fail Program Definition myReffix : natO -d> iProp triv_sig  := fixpoint myRec.


(*  Global Instance myRec_contractive : Contractive myRec.
  Proof.


    eapply discrete_funOF_contractive.
    split.
     solve_contractive. Qed. *)


Fail Program Definition myReffix : natO -d> iProp triv_sig  := fixpoint myRec.

Eval simpl in (fixpoint myRec).

(* fixpoints internal to the logic 
    https://plv.mpi-sws.org/coqdoc/iris/iris.bi.lib.fixpoint.html

Definition bi_least_fixpoint {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  tc_opaque (∀ Φ : A -n> PROP, □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)%I.

 *)


(* 
    fixpoint : ∀ A : ofe, Cofe A → Inhabited A → ∀ f : A → A, Contractive f → A

    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#fixpoint

    greatest and least fixpoint defined internally?
        https://plv.mpi-sws.org/coqdoc/iris/iris.bi.lib.fixpoint.html


    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#Contractive

    bi/PROP is a COFE 
        Global Instance bi_cofe (PROP : bi) : Cofe PROP := bi_cofe_aux PROP.
        https://plv.mpi-sws.org/coqdoc/iris/iris.bi.interface.html#bi_cofe

    
    the binary logical relation had to prove their persistent prop type is a COFE
      Global Instance persistent_pred_cofe : Cofe persistent_predO.


    beware this note on using "cannonical" "leibnizO" and "discreteO" in definitions
        https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.ofe.html#discrete_ofe


Useful definitions

    Pi types
        Definition discrete_fun {A} (B : A → ofe) := ∀ x : A, B x.
    
        Canonical Structure discrete_funO := Ofe (discrete_fun B) discrete_fun_ofe_mixin.

        Notation "A -d> B" := (@discrete_funO A (λ _, B)) 

        Global Instance discrete_funOF_contractive {C} (F : C → oFunctor) :
            (∀ c, oFunctorContractive (F c)) → oFunctorContractive (discrete_funOF F).

    Sigma types
        Context {A : ofe} {P : A → Prop}.

        Inductive sig (A:Type) (P:A -> Prop) : Type :=
            exist : forall x:A, P x -> sig P.
        
        Canonical Structure sigO : ofe := Ofe (sig P) sig_ofe_mixin.

        Global Instance sig_cofe `{!Cofe A, !LimitPreserving P} : Cofe sigO.

Definition World (sig1 : gmap nat type)(rho : gmap nat ) 

*)
(*      
        }
        admit.

    }
    rewrite lookup_partial_alter_ne.
    1:{
        rewrite lookup_empty.
        case (op None (c !!j)).
        - intros.
        destruct (c !! j).

    }


(* recursive predicates*)



    (* a singleton map should be valid if the only element is valid *)
    (* validity on maps is pointwise, so introduce an index j*)
    intros j.
    (* case on if i = j*)
    destruct (decide (i = j)).
    - rewrite e. rewrite lookup_partial_alter.
    rewrite Some_valid. exact vm.
    Focus 2.
    rewrite lookup_partial_alter_ne.
    + rewrite lookup_empty. reflexivity.
    Focus 2. exact n.
    (* now for the some case *)
    simplify_map_eq.
    (* if valid (op bempty c) 
      then c is valid *)
    apply cmra_valid_op_r in H.
    (* pointwise so again consider when i = j*)
    intros j.
    destruct (decide (i = j)).
    + rewrite e. rewrite lookup_merge.  rewrite lookup_partial_alter.
    simplify_map_eq.
    pose proof (H j).

    assert (c !! j = None \/ exists x , c !! j = Some x). {
        destruct (c !! j).
        - right. exists c0. reflexivity.
        - left. reflexivity.

    }
    destruct (H1).
    - rewrite H2. intros k. rewrite cmra_valid_validN in vm. 
        exact (vm k).
    - destruct H2. rewrite H2. intros k. rewrite cmra_valid_validN in vm.
    pose proof (vm k). 
    apply ra_valid_op_l in H3.
    assert 




    destruct (decide (c !! j = None)).
    - rewrite e. intros k. 
    rewrite cmra_valid_validN in vm. 
    pose proof (vm k). exact H1.
    - destruct (c !! j).
    {

    }

    
        pose proof (cmra_valid_validN vm).
    exact vm.
    Check c !! j.


    case (c !! j).
    - 
    destruct (c !! j).
    - 
    rewrite <- Some_op_opM.

     vm_compute.
     erewrite  partial_alter_merge_r.
    (* j <> i so index into singleton is invalid should result in None*)
    Check (lookup_partial_alter_ne (fun x => x) {[i := b]} i j n).
    eapply lookup_partial_alter_ne.

    - simplify_map_eq. simpl.
     (*resuls in "valid (Some b)" is valid if "valid b", which is by asumption*)
     compute.
    
    simplify_map_eq. rewrite lookup_partial_alter.
    compute.
*)


(* how do we allocate maps ? *)

Definition bmap_gfun : gFunctor. 
split with (constRF bmap).
eapply constRF_contractive.
Defined.

Definition bmap_sig : gFunctors := gFunctors.singleton bmap_gfun.

Global Instance bmap_in : inG bmap_sig bmap.
Proof.
    split with (inG_id := Fin.F1); eauto.
Qed.

Check empty.


(* allocate the empty map*)
Lemma allocMap :  ⊢@{iProp bmap_sig} |==> ∃ (γ : gname), own γ bempty.
Proof.
    iApply own_alloc.
    (* to allocate this map, it has to be valid*)
    exact bempty_valid.
Qed.


(* any valid anat can be allocated *)
Lemma allocanatt (an : anat):
    valid an -> 
     ⊢@{iProp anat_sig} |==> ∃ (γ : gname), own γ an.
Proof.
    intros.
    iApply own_alloc. 
    exact H.
Qed. 




(* 
https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/stdpp/fin_map_dom.v
    
    assert (m !! i = None) by (apply not_elem_of_dom; set_solver).

    
    gmap implements stdpp FinMap 
        https://plv.mpi-sws.org/coqdoc/stdpp//stdpp.fin_maps.html#FinMap

important properties 
    Lemma gmap_op m1 m2 : m1 ⋅ m2 = merge op m1 m2.

    Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
    
    Lemma lookup_core m i : core m !! i = core (m !! i).

    Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.

    Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.

    Lemma singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.

    Lemma singleton_core (i : K) (x : A) cx :
        pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.

    Lemma insert_op m1 m2 i x y :
        <[i:=x ⋅ y]>(m1 ⋅ m2) = <[i:=x]>m1 ⋅ <[i:=y]>m2.

    Lemma insert_merge (m1 : M A) (m2 : M B) i x y z :
        f (Some y) (Some z) = Some x →
        <[i:=x]>(merge f m1 m2) = merge f (<[i:=y]>m1) (<[i:=z]>m2).

    (* Disjoint 
        if maps are disjoint, then op = union of maps
    *)  
    Lemma gmap_op_union m1 m2 : m1 ##ₘ m2 → m1 ⋅ m2 = m1 ∪ m2.

    Lemma gmap_op_valid_disjoint m1 m2 :
    ✓ (m1 ⋅ m2) → (∀ k x, m1 !! k = Some x → Exclusive x) → m1 ##ₘ m2.

    Lemma dom_op m1 m2 : dom (m1 ⋅ m2) = dom m1 ∪ dom m2.

    Lemma dom_included m1 m2 : m1 ≼ m2 → dom m1 ⊆ dom m2.

    Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
        pred_infinite I →
        ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.

    Lemma alloc_updateP (Q : gmap K A → Prop) m x :
        ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
*)




Context `{Countable K} {A : cmra}.
(* the simplify_map _eq works here...*)

Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P →
  (∀ y, P y → Q (<[i:=y]>m)) →
  <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP; apply cmra_total_updateP=> n mf Hm.
  destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
  { generalize (Hm i). rewrite lookup_op. progress simplify_map_eq. 
    
    by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.





(* to talk about invariants or properties of owned resources, 
we need a namespace *)
Definition myName : namespace := nroot .@ "myName".
Check inv.
Check inv_alloc.
Eval simpl in (myName .@ 9).
(* Notation "N .@ x" := (ndot N x)
    .@ is syntax for ndot, an operation in stdpp namespace
*)
Eval simpl in (inv_alloc myName _).

(* we need additional struture in the resource algebra to talk about 
invariants 

Could not find an instance for "invGS_gen ?hlc myResourceFun".
*)
Fail Lemma makeInv : ⊢@{iProp myResourceFun} inv myName (True%I).

(* the structure can be found here
    https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.wsat.html#wsatGS
    
and is described in section 7.1.1 of Iris from the Ground Up

here wsat stands for "World Satisfaction"

the gFunctors for world satisfaction
  Definition wsatΣ : gFunctors :=
    #[GFunctor (gmap_viewRF positive (agreeRF $ laterOF idOF));
      GFunctor coPset_disjR;
      GFunctor (gset_disjR positive)].
*)
Check HasNoLc.
(* ignoring later credits for now*)
(* lets just assume it exists, I dont see how to construct concretely*)
Context `{! invGS_gen HasNoLc myResourceFun}.

Lemma makeInv : ⊢@{iProp myResourceFun} inv myName (True%I).
Admitted.



(*  See also section 6.3.2  *)

(* tying ghost state to physical state  
    Done via the authoritative camera pattern?
        6.3.3
*)
(* recursive propositions *)
(* higher order ghost state *)

(* how to use invariants for "world satisfaction"
    See section 7.1
*)

(* in order to have weakest preconditions for your language
you need to fill out this class

irisGS_gen 
https://plv.mpi-sws.org/coqdoc/iris/iris.program_logic.weakestpre.html#irisGS_gen
*)



(* just play with this for a second
https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.gen_heap.html#c31aa0e97544fe574310f89b0832e58f
*)


Definition mysig := gen_heapΣ loc type.
Check mysig.
Print gen_heapΣ.
(* gmap is from stdpp 
https://plv.mpi-sws.org/coqdoc/stdpp//stdpp.gmap.html#gmap_dep

gmap K V is an ofe 
    when K is countable
    and V is an OFE
https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.gmap.html#gmapO

gmap K V is a camera with a unit
    when K is countable 
    ans V is a cmra 
https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.gmap.html#gmapUR

There is a special kind of gmap, a ghostmap
    Definition ghost_mapΣ (K V : Type) `{Countable K} : gFunctors :=
        #[ GFunctor (gmap_viewR K (agreeR (leibnizO V))) ].

This uses a view camera
    https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.view.html#view

    what is that?

    Record view {A B} (rel : nat → A → B → Prop) :=
    View { view_auth_proj : option (dfrac × agree A) ; view_frag_proj : B }.

    with 
        Notation "●V dq a" := (view_auth dq a)
        Notation "◯V a" := (view_frag a) (at level 20).
    with
        Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
            View (Some (dq, to_agree a)) ε.
        Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := 
            View None b.


    uses a view relation?
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

    the specific view relation for gmaps
        Local Canonical Structure gmap_view_rel : view_rel (gmapO K V) (gmap_view_fragUR K V) :=
    where
        Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
            gmapUR K (prodR dfracR V).
    
    finally
        Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra :=
         viewR (gmap_view_rel K V).

This map also uses the agree algebra
    Definition ghost_mapΣ (K V : Type) `{Countable K} : gFunctors :=
        #[ GFunctor (gmap_viewR K (agreeR (leibnizO V))) ]

    Intuition, only resources that are equivalent can be combined
    Usage with heaps:
        The usefulness of the agree construction is demonstrated by the fact
        that it is used to define the resource of heaps. The inclusion of the
        agree RA allows us to conclude that if we have two points-to
        predicates for the same location, [l ↦{dq1} v1] and [l ↦{dq2} v2],
        then they _agree_ on the value stored at the location: [v1 = v2].

*)

(* this is a statement in a logic where the resource is a 
physical heap, ghost heap,  *)
Lemma asm (P : iProp mysig) : P ⊢ P.
Proof.
    iIntros "H".
    iApply "H".
Qed.


(* 
(* https://coq.inria.fr/doc/V8.19.0/refman/language/extensions/canonical.html#canonicalstructures*)
Canonical Structure typeO := leibnizO type.
Print discreteR.
Check typeO.

Lemma type_ra_mixin : RAMixin type.
Canonical Structure typeO := discreteR typeO.

(* this is an ofe.. make it a camera*)

Print loc.
Check gmapR.
Print discreteR.
Eval simpl in (gmapR natO typeO).
Canonical Structure typeStoreO := g

(* a 4 tuple 
    2 type stores, 
    a mapping from type variables to a product of type variables
    a mapping from type variables to a 3 tuple (type, type, relation)
*)

Check prodO.
Canonical Structure world0 := prodO typeO typeO. *)
