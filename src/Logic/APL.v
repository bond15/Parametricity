
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import stdpp.base.

From iris.proofmode Require Import base .

From MyProject.src.Logic Require Import SysF typing.

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

    Import SysF.
    Import typing.

    Definition ty (t : type) : Type := sig (fun (e : expr) => typed [] e t).

    Definition Rel (t1 t2 : type) {P : Type} : Type := ty t1 -> ty t2 -> P.
    Definition Rel' {P : Type} : Type := @sigT (prod type type)(fun p => @Rel p.1 p.2 P).

    Definition Raw_Rel {PROP : Type} : Type := (expr * expr) -> PROP.

    Section laws.
        Context {PROP : Type}.
    
        Context {apl_entails : PROP -> PROP -> Prop}.
        Context {apl_and : PROP -> PROP -> PROP}.
        Context {apl_emp : PROP}.
        Context {apl_imp: PROP -> PROP -> PROP}.
        Context {apl_forall : forall A, (A -> PROP) -> PROP}.
        Context {apl_forall_term : forall (t : type), (ty t -> PROP) -> PROP}.
        Context {apl_forall_type : (type -> PROP) -> PROP}.
        Context {apl_rel_sub : type -> list (@Rel' PROP) -> @Rel' PROP}.
        Context {apl_rel_sub' : type -> list (@Raw_Rel PROP) -> @Raw_Rel PROP}.

        Bind Scope apl_scope with PROP.


        Local Infix "⊢" := apl_entails.
        Local Infix "∧" := apl_and : apl_scope.
        Local Infix "→" := apl_imp : apl_scope.

        Definition apl_iff (P Q : PROP) : PROP := 
            apl_and (apl_imp P Q) (apl_imp Q P).

        Definition apl_rel_iff {t1 t2 : type} (R1 R2 : @Rel t1 t2 PROP) : PROP := 
        apl_forall_term t1 (fun tm1 => 
        apl_forall_term t2 (fun tm2 => 
            apl_iff (R1 tm1 tm2) (R2 tm1 tm2))).

        Definition Rel_to_Rel' (t1 t2 : type) (R : @Rel t1 t2 PROP) : @Rel' PROP := 
            existT (pair t1 t2) R.

        Record AplLaws := {
            apl_entails_po : PreOrder apl_entails ;

            apl_and_elim_l P Q : P ∧ Q ⊢ P;
            apl_and_elim_r P Q : P ∧ Q ⊢ Q;
            apl_and_intro P Q R : (P ⊢ Q) -> (P ⊢ R) -> P ⊢ Q ∧ R;

            apl_impl_intro_r P Q R : (P ∧ Q ⊢ R) -> P ⊢ Q → R;
            apl_impl_elim_l' P Q R : (P ⊢ Q → R) -> P ∧ Q ⊢ R;

            apl_forall_intro {A} P (Ψ : A -> PROP) : 
                (forall a, P ⊢ Ψ a) -> P ⊢ apl_forall _ (fun a => Ψ a );

            apl_forall_elim {A} {Ψ : A -> PROP} a : apl_forall _ (fun a => Ψ a ) ⊢ Ψ a;

            apl_forall_term_intro {t} P (Ψ : ty t -> PROP) : 
                (forall tm, P ⊢ Ψ tm) -> P ⊢ apl_forall_term _ (fun tm => Ψ tm );

            apl_forall_term_elim {t} {Ψ : ty t -> PROP} a : apl_forall_term _ (fun a => Ψ a ) ⊢ Ψ a;

            apl_forall_type_intro P (Ψ : type -> PROP) : 
                (forall t, P ⊢ Ψ t) -> P ⊢ apl_forall_type (fun t => Ψ t );

            apl_forall_type_elim  {Ψ : type -> PROP} t : apl_forall_type (fun t => Ψ t ) ⊢ Ψ t;

(*             (* relational substitution laws *)
            apl_rel_sub_arrow (rho : list (@Rel' PROP)) (t1 t2 : type) : 
                apl_emp ⊢ (@apl_rel_iff t1 t2 
                    (apl_rel_sub (TArrow t1 t2) rho) 
                    (apl_rel_sub (TArrow t1 t2) rho)) ; *)

        }.
    End laws.
    Check sig.
    Print prod.




    Structure apl := APL {
        apl_car :> Type@{Logic};
        apl_entails : apl_car -> apl_car -> Prop;
        apl_emp : apl_car;
        (* 
            this gets mapped to "interp"?, 
            the definition of the binary logical relation on exrpessions
         *)
        apl_rel_sub : type -> list (@Rel' apl_car) -> @Rel' apl_car;
        (* equality *)
        (* relations *)
        apl_imp : apl_car -> apl_car -> apl_car ;
        apl_forall :  forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* forall term *)
        apl_forall_term : forall (t : type), (ty t -> apl_car) -> apl_car;
        (* forall type *)
        apl_forall_type : (type -> apl_car) -> apl_car;
        (* forall rel *)
        apl_forall_rel : forall {t1} {t2}, ((@Rel t1 t2 apl_car) -> apl_car) -> apl_car; 
        apl_and : apl_car -> apl_car -> apl_car;
        apl_or : apl_car -> apl_car -> apl_car;
        apl_exist : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists term *)
(*         apl_exist_term : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists type *)
        apl_exist_type : forall A : Type@{Quant}, (A -> apl_car) -> apl_car;
        (* exists rel *)
        apl_exist_rel : forall A : Type@{Quant}, (A -> apl_car) -> apl_car; *)
        apl_laws : @AplLaws apl_car apl_entails apl_and apl_imp apl_forall apl_forall_term apl_forall_type
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

    Notation "∀ x .. y , P" :=
    (apl_forall (λ x, .. (apl_forall (λ y, P%A)) ..)) : apl_scope.
    Notation "∃ x .. y , P" :=
    (apl_exist (λ x, .. (apl_exist (λ y, P%A)) ..)) : apl_scope. 

Check apl_forall_type _.
    Notation "∀ty x , P" :=
    (apl_forall_type _ (λ x, P%A))  (at level 100) : apl_scope.


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

(* Lemma instance : @AplLaws Prop imp and imp all.
Proof.
    constructor; unfold imp in *.
    (* These laws already exist in Logic module *)
    2:{ intros P Q [P' Q']. exact P'.  }
    6:{ intros. unfold all. intros. pose proof (H x H0). exact H1. }
Admitted.
 *)
 Import typing.

Definition all_term : forall (t : type), (ty t -> Prop) -> Prop := 
fun t P => (forall e, P e).

(* Lemma instance : apl.
    apply (APL Prop imp True imp all all_term (@all type) and or ex).
    constructor.
    10:{
        intros. unfold imp. intros. unfold all_term in H. exact (H a).
    }
    9:{
        intros. unfold imp. intros. unfold all_term. intros. exact (H e H0).
    }
Abort. *)

Section huh.
    Context {PROP : apl}.
    Check @apl_imp PROP.
    Check apl_imp.
    Notation "P ⊢ Q" := (@apl_entails PROP P%A Q%A) : stdpp_scope.
    Infix "∧" := (@apl_and PROP ): apl_scope.

    Check imp.


Fail Lemma  thing (P Q : PROP) : ⊢ ((Q → True) ∧ Q)%A.

Lemma thing P Q  : P ∧ (P → Q) ⊢ Q.
Proof.
    Check apl_and_intro (apl_laws PROP).
    Check apl_impl_elim_l' (apl_laws PROP).
    apply (apl_impl_elim_l' (apl_laws PROP)).
Abort.

(* Lemma foo P : ⊢ @apl_forall PROP term (fun x => P).
Proof.
    apply (apl_forall_intro (apl_laws PROP)).
    intros.
    Check apl_forall_intro (apl_laws PROP).
Check @apl_forall PROP term.
Abort. *)

Lemma foo P : ⊢ @apl_forall_type PROP (fun x => P x).
Proof.
    apply (apl_forall_type_intro (apl_laws PROP)).
    intros.
(*     eapply (apl_forall_type_elim (apl_laws PROP)).
    intros *)
Abort.
End huh.
Section tactics.
    Context {PROP  : apl}.

    Inductive env : Type :=
    | Enil : env 
    | Esnoc : env  → ident → PROP → env .

    Fixpoint env_lookup (i : ident) (Γ : env ) : option PROP :=
    match Γ with
    | Enil => None
    | Esnoc Γ j x => if ident_beq i j then Some x else env_lookup i Γ
    end.

    Notation "Γ !! j" := (env_lookup j Γ).

    Fixpoint env_delete  (i : ident) (Γ : env) : env :=
    match Γ with
    | Enil => Enil
    | Esnoc Γ j x => if ident_beq i j then Γ else Esnoc (env_delete i Γ) j x
    end.


    Inductive env_wf  : env → Prop :=
    | Enil_wf : env_wf Enil
    | Esnoc_wf Γ i x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ i x).


(*     Global Arguments Enil {_}.
    Global Arguments Esnoc {_} _ _ _.
    Global Instance: Params (@Enil) 1 := {}.
    Global Instance: Params (@Esnoc) 1 := {}. *)

    Definition of_envs' {PROP : apl} (Γ : env) : PROP := emp.
   (*  (⌜envs_wf' Γp Γs⌝ ∧ env_and_persistently Γp )%A. *)

  Global Instance: Params (@of_envs') 1 := {}.
  Definition of_envs {PROP : apl} (Δ : env ) : PROP :=
    of_envs' Δ .
  Global Instance: Params (@of_envs) 1 := {}.
  Global Arguments of_envs : simpl never.
  
  Local Definition pre_envs_entails_def {PROP : apl} (Γ : env) (Q : PROP) :=
    of_envs' Γ ⊢ Q.
  Local Definition pre_envs_entails_aux : seal (@pre_envs_entails_def).
  Proof. by eexists. Qed.
  Local Definition pre_envs_entails := pre_envs_entails_aux.(unseal).
  Local Definition pre_envs_entails_unseal :
  @pre_envs_entails = @pre_envs_entails_def := pre_envs_entails_aux.(seal_eq).

    Definition envs_entails {PROP : apl} (Δ : env) (Q : PROP) : Prop :=
  pre_envs_entails PROP Δ  Q.

Definition envs_entails_unseal :
  @envs_entails = λ PROP (Δ : env ) Q, (of_envs Δ ⊢ Q).
  Proof. unfold envs_entails. Admitted.



Global Arguments envs_entails {PROP} Δ Q%_A.
Global Instance: Params (@envs_entails) 1 := {}.

Lemma tac_start {P : PROP} : envs_entails (Enil) P → ⊢ P.
Proof.
  rewrite envs_entails_unseal. unfold of_envs. unfold of_envs'. intros. done.
Qed.

Lemma tac_pure  Δ i P (φ : Prop) (Q : PROP) :
  env_lookup i Δ = Some P →

  (φ → envs_entails (env_delete i  Δ) Q) → envs_entails Δ Q.
Proof. 
    intros.
    rewrite envs_entails_unseal.
    rewrite envs_entails_unseal in H0.
Admitted.

End tactics.

Section test.
    Context {PROP : apl}.
    Lemma thing (P Q : PROP)  : ⊢ ((P ∧ (P → Q)) → Q).
Abort.
(*         apply (apl_impl_intro_r (apl_laws PROP)).
        pose proof ()
        apply tac_start.

        eapply tac_pure.

        rewrite envs_entails_unseal.
        unfold of_envs.
        unfold of_envs'.

 *)
End test.

