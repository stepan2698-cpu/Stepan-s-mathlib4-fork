/-
Copyright (c) 2026 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib

/-!
# Semisimple representations

This file defines semisimple monoid representations.

-/

namespace Representation

@[expose] public section

open scoped MonoidAlgebra

universe u v w

variable {k G V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- A representation is semisimple when every subrepresentation has a complement, or equivalently,
  the representation is a direct sum of irreducible representations. -/
@[mk_iff] class IsSemisimpleRepresentation extends
  ComplementedLattice (Subrepresentation ρ)

theorem isSemisimpleRepresentation_iff_isSemisimpleModule_asModule :
    IsSemisimpleRepresentation ρ ↔ IsSemisimpleModule k[G] ρ.asModule := by
  rw [isSemisimpleModule_iff, isSemisimpleRepresentation_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.subrepresentationSubmoduleOrderIso

theorem isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule (M : Type*) [AddCommGroup M]
    [Module k[G] M] : IsSemisimpleModule k[G] M ↔
    IsSemisimpleRepresentation (ofModule (k := k) (G := G) M) := by
  rw [isSemisimpleModule_iff, isSemisimpleRepresentation_iff]
  exact OrderIso.complementedLattice_iff Subrepresentation.submoduleSubrepresentationOrderIso

theorem isSemisimpleRepresentation_of_isIrreducible (h : IsIrreducible ρ) :
    IsSemisimpleRepresentation ρ := by
  rw [irreducible_iff_isSimpleModule_asModule] at h
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

instance [h : IsIrreducible ρ] : IsSemisimpleRepresentation ρ :=
  isSemisimpleRepresentation_of_isIrreducible ρ h

end

variable {k G V : Type*} [Group G] [Fintype G] [Field k] [NeZero (Fintype.card G : k)]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)

theorem isSemisimpleRepresentation_of_card_neZero : IsSemisimpleRepresentation ρ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

instance : IsSemisimpleRepresentation ρ := isSemisimpleRepresentation_of_card_neZero ρ

end Representation
