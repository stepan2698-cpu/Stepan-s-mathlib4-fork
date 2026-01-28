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

@[expose] public section

variable {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- A representation is semisimple when every subrepresentation has a complement, or equivalently,
  the representation is a direct sum of irreducible representations. -/
@[mk_iff] class IsSemisimpleRepresentation extends
  ComplementedLattice (Subrepresentation ρ)
