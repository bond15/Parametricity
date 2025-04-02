From iris.algebra Require Export gmap ofe cofe_solver .
From MyProject.src.SystemG Require Export SystemG persistent_pred.
From iris.base_logic Require Import iprop upred .

Module Gtypes.

(* guarded type *)


(* 
Fail Fixpoint stype (n : nat) : Prop :=
match n with 
| O => False
| S k => forall (j : nat)(phi : gmap loc (stype k))(v : val) , j ≤ k /\ storeType j phi
end
with storeType (k : nat)(phi : gmap loc (stype k)) : Prop := forall (l in dom phi), stype k ... phi l = . *)


Inductive stype (n : nat) : gmap loc (stype)


    Context `{Σ : gFunctors}.

Definition TypeF : oFunctor := (gmapOF loc (▶idOF) * valO -n> iPropO Σ)%OF.

Definition TypeO : solution (TypeF) := solver.result _.

Definition Type' : ofe := oFunctor_apply TypeF TypeO.
Definition fold : TypeO -n> Type' := ofe_iso_2 TypeO.
Definition unfold : Type' -n> TypeO := ofe_iso_1 TypeO.

Example base : Type'.
unfold Type'. simpl.  

(laterO TypeO).
apply Next. apply unfold. unfold Type'. simpl.

Example foo  : prodO (gmapO loc (laterO TypeO)) valO.
constructor.
{
  exact  {[ 3 :=  ]} .
}
Program Example foo : prodO (gmapO loc (laterO TypeO)) valO -n> iPropO Σ := 
λne p, match p with 
      | (phi , v) => True%I 
end.


Example ty : Type'.
unfold Type'.
simpl.



Check solution.
(* profuntor from Cofe to Ofe ? *)
Print oFunctor.
Check idOF.
Check prodOF.
Check ofe_morOF.
Check constOF.
Check sumOF.
Check laterOF.
Check discrete_funOF.
Check sigTOF.
(* good, components to form a poly functor out of, then take guarded fix *)

(* reverse engineering the definition of iProp ... a solver for guarded domain equation ..?
 https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.iprop.html#iProp_solution_sig *)


 Fail Inductive Illegal : Set := 
 | foo :(Illegal -> Illegal) -> Illegal
 | bar : () .

(* theres a coersion from (X : ofe) to constOF X *)
Definition legal : oFunctor := (▶ (∙ -n> ∙)) + unitO.

(* sick... this works most of the time... with the exception of missing typeclass instance not in scope
for complicated OFEs *)
Definition LegalO : solution (legal) := solver.result _.

Definition Legal : ofe := oFunctor_apply legal LegalO.

Check ofe_iso_1 LegalO.
Definition fold : LegalO -n> Legal := ofe_iso_2 LegalO.
Definition unfold : Legal -n> LegalO := ofe_iso_1 LegalO.
(* nice, syntax for writing non expansive morphisms*)
Example foo : Legal := inl (Next (λne (x : LegalO), x)).

Program Definition  bar : Legal -n> Legal := 
λne (x : Legal), 
  (match x with 
    | inl (Next f) => fold (f (unfold (inr ())))(*  illegal  *)
    | inr () => x
  end).
Next Obligation.
unfold Proper. red. intros.
destruct H.
{ intros. try rewrite -H. destruct H. admit. } (* only know that f is equal after at least one timestep *)
destruct y1, y2. eauto.
Abort.

(* cursed *)
Definition zero : Legal := inr ().
Program Definition suc : Legal -n> Legal := λne l, inl (Next (λne _, unfold l)).
Next Obligation.
  unfold Proper. red. intros.
  destruct H.

(* guarded stream  *)

Definition StreamF (A : ofe)`{_ : Cofe A} : oFunctor := A  * (laterOF ∙).

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


End Gtypes.