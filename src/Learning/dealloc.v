
From stdpp Require Import base gmap.

From iris.base_logic Require Import invariants iprop upred saved_prop.
From iris.algebra Require Import gset_bij excl gmap gset cmra ofe.
From iris.proofmode Require Import proofmode.

(* try to show deallocation

    m1 := {[0 := true ; 1 := false]}
    m2 := {[0 := true]}

    m2 <= m1 

    m2 ~~> m1
*)

(* 
heap lang

    The state: heaps of option vals, with None representing deallocated locations.
        Record state : Type := {
            heap: gmap loc (option val);
            used_proph_id: gset proph_id;
        }.

https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lang.html#heap_lang.FreeS

  | FreeS l v σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Free (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=None]> σ)
               []


general properties of delete for maps
    https://plv.mpi-sws.org/coqdoc/stdpp//stdpp.fin_maps.html#lookup_delete


For gmap Camera
    The function delete delete k m should delete the value at key k in m. 
    If the key k is not a member of m, the original map should be returned.
        Class Delete (K M : Type) := delete: K → M → M.

    delete_update
        : ∀ (m : gmap ?K ?A) (i : ?K), m ~~> delete i m
        where
            ?K : [ |- Type]
            ?EqDecision0 : [ |- EqDecision ?K]
            ?H : [ |- Countable ?K]
            ?A : [ |- cmra]

    gmap_view.gmap_view_delete:
    ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {V : cmra} 
    (m : gmap K V) (k : K) (v : V),
gmap_view.gmap_view_auth (DfracOwn 1) m ⋅ gmap_view.gmap_view_frag k (DfracOwn 1) v ~~>
gmap_view.gmap_view_auth (DfracOwn 1) (delete k m)


delete_singleton_local_update:
∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : cmra} (m : gmap K A) (i : K) (x : A),
Exclusive x → (m, {[i := x]}) ~l~> (delete i m, ∅)


gmap_view.gmap_view_delete_big:
∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {V : cmra} (m m' : gmap K V),
gmap_view.gmap_view_auth (DfracOwn 1) m ⋅ ([^ op map] k↦v ∈ m', gmap_view.gmap_view_frag k (DfracOwn 1) v) ~~>
gmap_view.gmap_view_auth (DfracOwn 1) (m ∖ m')

*)

Print optionR.
(* normal state, ghost state after *)
Definition m1 : gmap nat (option bool) := {[ 0 := Some true ; 1 := Some false]}.
Definition m2 : gmap nat (option bool) := {[ 0 := Some true ]}.

(* Example dealloc_gmap (m : gmap nat (option bool)) (n : nat) : gmap nat (option bool)
    :=  <[n := None]>m. *)

    Check delete.
Example dealloc_ex : delete 1 m1 = m2 .
Proof.
    unfold delete. unfold map_delete. 
    unfold m1.
    vm_compute.
    reflexivity.
Qed.

(* This makes sense as a normal map.. but how does this work as a camera..? *)
Lemma delete_update {K : Type}`{ Countable K} {A : cmra} (m : gmapR K A) i : m ~~> delete i m.
Proof.
    Check cmra_total_update.
  apply cmra_total_update=> n mf Hm j; destruct (decide (i = j)); subst.
  - move: (Hm j). repeat rewrite lookup_op.  rewrite !lookup_delete. 
    rewrite left_id.
    apply cmra_validN_op_r.
(*    rewrite !lookup_op lookup_delete left_id.
    apply cmra_validN_op_r. *)
  - move: (Hm j).
    rewrite !lookup_op. (* same as repeat *)
    rewrite lookup_delete_ne. 
    done. done.
Qed.


(* ok... but.. 
 what camera can we use here... 

 Is it possible in heap lang to show that ...
 {[ i := 2]} ~~> {[]} ~~> {[ i = 1]}
 ?

 Heap lang state
    The state: heaps of option vals, with None representing deallocated locations.
        Record state : Type := {
            heap: gmap loc (option val);
            used_proph_id: gset proph_id;
        }.

ghost state
   Definition gen_heap_interp (σ : gmap loc (option val)) : iProp Σ := ∃ m : gmap loc gname,
    
    ⌜ dom m ⊆ dom σ ⌝ ∗
    ghost_map_auth (gen_heap_name hG) 1 σ ∗
    ghost_map_auth (gen_meta_name hG) 1 m.


Local Definition ghost_map_auth_def
      (γ : gname) (q : Qp) (m : gmap loc (option val)) : iProp Σ :=
    own γ (gmap_view_auth (V:=agreeR $ leibnizO (option val)) (DfracOwn q) (to_agree <$> m)).


No.. because agreeR is used here...?
*)

Check optionO.
(* Definition ghost : cmra := gmapR nat (agreeR $ leibnizO (option bool)).
 *)
Definition ghost : cmra := gmapR nat (agreeR $ optionO boolO).

Definition gm1 : ghost := {[ 0 := to_agree $ Some true]}.
Definition gm2 : ghost := delete 0 gm1.
Definition gm2' : ghost := empty.
Definition gm2'' : ghost := {[ 0 := to_agree $ None ]}.
Definition gm3 : ghost := {[ 0 := to_agree $ Some false]}.

Example t1 : gm1 ~~> gm2.
Proof.
    apply delete_update.
Qed.

Example gm2eq : gm2 = gm2'.
Proof.
    vm_compute.
    done.
Qed.

Check exclR.
Print exclR.

(* 
Lemma cmra_update_exclusive `{!Exclusive x} y:
  ✓ y → x ~~> y.

*)
Check insert_update.

Print excl.
Definition emap : cmra := gmapR nat (exclR $ optionO bool).
Definition em1 : emap := {[ 0 := Excl $ Some true ]}.
Definition em2 : emap := delete 0 em1.
Definition em2': emap := empty.
Definition em2'':emap := {[ 0 := Excl $ None]}.
Definition em3 : emap := {[ 0 := Excl $ Some false ]}.

Lemma em2eq : em2 = em2' .
Proof.
    vm_compute.
    done.
Qed. 

Example et1 : em1 ~~> em2.
Proof.
    apply delete_update.
Qed.

Example et1' : em1 ~~> em2''.
Proof.
    apply insert_update.
    apply cmra_update_exclusive.
    done.
Qed.

Example et2' : em2'' ~~> em3.
Proof.
    apply insert_update.
    apply cmra_update_exclusive.
    done.
Qed.

(* directly *)

Example direct : {[ 0 := Excl $ Some true]} ~~> {[ 0 := Excl $ Some false]}.
Proof.
    apply insert_update.
    apply cmra_update_exclusive.
    done.
Qed.

(* or using dfrac *)

Print dfrac.

(* 

Local Instance excl_op_instance : Op (excl A) := λ x y, ExclInvalid.

*)
Example et2 : em2 ~~> em3.
Proof.
    rewrite em2eq.
    unfold em2'. unfold em3.
    Check insert_update.
    Check alloc_unit_singleton_update.
    apply (alloc_unit_singleton_update (Excl None)).
    3:{
        apply cmra_update_exclusive.
        done.
     }
     done.
    unfold LeftId.
    intros.
    destruct x.
    - destruct o.
    + destruct o.
    * simpl.

    done.
    apply insert_update.



(* 
    {[ 0 := None ]} <> {[ 0 := to_agree None]}
*)
Example gm2e1' : gm2' = gm2''.
Proof.
    vm_compute.
Abort.

Check insert_update.

Example nope : gm2 ~~> gm3 -> False.
Proof.
    intros. 
    unfold cmra_update in *.
    rewrite gm2eq in H.
    unfold gm2' in H.
    unfold gm3 in H.
    pose proof (H 0 (Some {[ 0 := to_agree None]})).
    simpl in H0.
    Check gmap_op.
    rewrite !gmap_op in H0.
    Search merge.
    rewrite !merge_empty_l in H0.
    simpl in H0.
    
    assert (✓{0} (∅ ⋅ {[0 := to_agree (None : option bool)]}) ).

Example t2 : gm2 ~~> gm3.
Proof.
    rewrite gm2eq.
    unfold gm2'.
    unfold gm3.

    unfold cmra_update.
    intros.
    destruct mz.
    -
    simpl. simpl in H.
    move: H.

    apply cmra_validN_op_r.
    eapply alloc_unit_singleton_update.
    - unfold valid. 
    apply insert_update.


