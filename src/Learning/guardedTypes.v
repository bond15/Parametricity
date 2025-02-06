From iris.algebra Require Export ofe cofe_solver .

Module Gtypes.

(* guarded type *)


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
Definition legal_sol : solution (legal) := solver.result _.

Definition Legal : ofe := oFunctor_apply legal legal_sol.

Example foo : Legal := inl (Next (λne x, x)).


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