
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import stdpp.base.

Reserved Notation "'emp'".
Reserved Notation "(⊢)" (at level 99).
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P ∧ Q" (at level 80, right associativity, format "P '/' ∧ '/' Q").
Reserved Notation "P ∨ Q" (at level 85, right associativity, format "P '/' ∨ '/' Q").
Reserved Notation "P → Q"
(at level 99, Q at level 200, right associativity,
 format "'[' P '/' → '/' '[' Q ']' ']'").



Local Set Primitive Projections.
Module APL.
    Universe Logic.
    Universe Quant.

    Section laws.
        Context {PROP : Type}.
    
        Context {apl_entails : PROP -> PROP -> Prop}.
        Context {apl_and : PROP -> PROP -> PROP}.
        Context {apl_imp: PROP -> PROP -> PROP}.
        Context {apl_forall : forall A, (A -> PROP) -> PROP}.

        Bind Scope apl_scope with PROP.


        Local Infix "⊢" := apl_entails.
        Local Infix "∧" := apl_and : apl_scope.
        Local Infix "→" := apl_imp : apl_scope.

        Record AplLaws := {
            apl_entails_po : PreOrder apl_entails ;

            apl_and_elim_l P Q : P ∧ Q ⊢ P;
            apl_and_elim_r P Q : P ∧ Q ⊢ Q;
            apl_and_intro P Q R : (P ⊢ Q) -> (P ⊢ R) -> P ⊢ Q ∧ R;

            apl_impl_intro_r P Q R : (P ∧ Q ⊢ R) -> P ⊢ Q → R;
            apl_impl_elim_l' P Q R : (P ⊢ Q → R) -> P ∧ Q ⊢ R;

            apl_forall_term_intro {A} P (Ψ : A -> PROP) : 
                (forall a, P ⊢ Ψ a) -> P ⊢ apl_forall _ (fun a => Ψ a );
        }.
    End laws.

    Structure apl := APL {
        apl_car :> Type@{Logic};
        apl_entails : apl_car -> apl_car -> Prop;
        apl_emp : apl_car;
        (* equality *)
        (* relations *)
        apl_imp : apl_car -> apl_car -> apl_car ;
        apl_forall :  forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
(*         (* forall term *)
        apl_forall_term : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* forall type *)
        apl_forall_type : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* forall rel *)
        apl_forall_rel : forall A : Type@{Quant}, (A -> apl_car) -> apl_car; *)
        apl_and : apl_car -> apl_car -> apl_car;
        apl_or : apl_car -> apl_car -> apl_car;
        apl_exist : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists term *)
(*         apl_exist_term : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists type *)
        apl_exist_type : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists rel *)
        apl_exist_rel : forall A : Type@{Quant}, (A -> apl_car) -> apl_car; *)
        apl_laws : @AplLaws apl_car apl_entails apl_and apl_imp apl_forall
    }.

    Declare Scope apl_scope.
    (* https://plv.mpi-sws.org/coqdoc/iris/iris.bi.interface.html#bi_cofe *)
    Delimit Scope apl_scope with A.
    Bind Scope apl_scope with apl_car.

    Global Instance: Params (@apl_entails) 1 := {}.
    Global Instance: Params (@apl_emp) 1 := {}.
    Global Instance: Params (@apl_and) 1 := {}.
    Global Instance: Params (@apl_imp) 1 := {}.
    Global Instance: Params (@apl_forall) 2 := {}.
    Global Instance: Params (@apl_exist) 2 := {}.

    Global Arguments apl_car : simpl never.
    Global Arguments apl_entails {PROP} _ _ : simpl never, rename.
    Global Arguments apl_emp {PROP} : simpl never, rename.
    Global Arguments apl_and {PROP} _ _ : simpl never, rename.
    Global Arguments apl_or {PROP} _ _ : simpl never, rename.
    Global Arguments apl_imp {PROP} _ _ : simpl never, rename.
    Global Arguments apl_forall {PROP _} _%_A : simpl never, rename.
    Global Arguments apl_exist {PROP _} _%_A : simpl never, rename.

    Notation "'emp'" := (apl_emp) : apl_scope.
    Infix "∧" := apl_and : apl_scope.
    Notation "(∧)" := apl_and (only parsing) : apl_scope.
    Infix "∨" := apl_or : apl_scope.
    Notation "(∨)" := apl_or (only parsing) : apl_scope.
    Infix "→" := apl_imp : apl_scope.
(* 
    Notation "∀ x .. y , P" :=
    (apl_forall (λ x, .. (apl_forall (λ y, P%I)) ..)) : apl_scope.
    Notation "∃ x .. y , P" :=
    (apl_exist (λ x, .. (apl_exist (λ y, P%I)) ..)) : apl_scope. *)
    Notation "(⊢)" := apl_entails (only parsing) : stdpp_scope.
    Notation "P ⊢ Q" := (apl_entails P%A Q%A) : stdpp_scope.

    Definition apl_emp_valid {PROP : apl} (P : PROP) : Prop := emp ⊢ P.

    Global Arguments apl_emp_valid {_} _%_A : simpl never.
    Global Typeclasses Opaque apl_emp_valid.
    
    Notation "⊢ Q" := (apl_emp_valid Q%A) (at level 99) : stdpp_scope.
(*     Notation "'⊢@{' PROP } Q" := (apl_emp_valid (PROP:=PROP) Q%I) (only parsing) (at level 99): stdpp_scope.
 *)

    (* https://plv.mpi-sws.org/coqdoc/iris/iris.bi.interface.html#::bi_scope:'emp' *)

    

    Check apl_and.
    Fail Definition thing P Q  := (True ∧ Q)%A.
    Fail Definition thing P Q  := (⊢ P ∧ Q)%A.
 
End APL.

Import APL.
Check @AplLaws.

Check or.
Locate and.

(* Woah...  *)
Print Logic.


Definition imp (A B : Prop) := forall (_ : A ), B.

Check @AplLaws Prop imp and imp all.

Lemma instance : @AplLaws Prop imp and imp all.
Proof.
    constructor; unfold imp in *.
    (* These laws already exist in Logic module *)
    2:{ intros P Q [P' Q']. exact P'.  }
    6:{ intros. unfold all. intros. pose proof (H x H0). exact H1. }
Admitted.

Section huh.
    Context {PROP : apl}.
    Context {term : Type}.
    Check @apl_imp PROP.
    Check apl_imp.
    Notation "P ⊢ Q" := (@apl_entails PROP P%A Q%A) : stdpp_scope.
    Infix "∧" := (@apl_and PROP ): apl_scope.

    Check imp.


Fail Lemma  thing (P Q : PROP) : ⊢ ((Q → True) ∧ Q)%A.

Lemma thing P Q  : P ∧ (P → Q)⊢ Q.
Proof.
    Check apl_and_intro (apl_laws PROP).
    Check apl_impl_elim_l' (apl_laws PROP).
    apply (apl_impl_elim_l' (apl_laws PROP)).
Abort.

Lemma foo P : ⊢ @apl_forall PROP term (fun x => P).
Proof.
    apply (apl_forall_term_intro (apl_laws PROP)).
    intros.
    Check apl_forall_term_intro (apl_laws PROP).
Check @apl_forall PROP term.