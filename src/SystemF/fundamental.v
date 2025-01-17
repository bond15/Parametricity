From MyProject.src.SystemF Require Export SysF typing rules logrel.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import upred iprop.
From iris.prelude Require Import options.
From iris.program_logic Require Import adequacy.

From iris.base_logic Require Import invariants.

Context `{irisGS SysF_lang Σ}.

Import SysF.
Import typing.
Import logrel.
Print tc_opaque.

Notation "⟦ τ ⟧" := (interp τ).

Notation "⟦ Γ ⟧*" := (interp_env Γ).

Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).

Definition bin_log_related (gamma : list type)(e e' : expr)(t : type) : iProp Σ :=
    (□ ∀ rho gammas, 
        ⟦ gamma ⟧* rho gammas -∗
        ⟦ t ⟧ₑ rho (e.[env_subst (gammas.*1)], e'.[env_subst (gammas.*2)]))%I.
    