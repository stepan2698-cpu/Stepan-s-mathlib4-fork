/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

import mathlib

open scoped TensorProduct

/-!
# Absolutely simple modules
-/

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommMonoid M]
    [Module A M] [Module k M] [IsScalarTower k A M]
variable {k' : Type*} [CommRing k'] [Algebra k k']

--#synth Module (A ⊗[k] k') (M ⊗[k] k')

/-private def baseChangeSmul {k' : Type u} [Field k'] [Algebra k k'] :
    k' ⊗[k] A →+ k' ⊗[k] M →+ k' ⊗[k] M := by
  apply TensorProduct.liftAddHom
  · sorry
  · sorry

local instance {k' : Type u} [Field k'] [Algebra k k'] : Module (k' ⊗[k] A) (k' ⊗[k] M) where
  smul := by
    sorry
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- If `A` is an algebra over a field `k`, then an `A`-module `M` is called **absolutely simple,
if for any field extension `k'` of `k`, `k' ⊗[k] M` is a simple `k' ⊗[k] A`-module. -/
@[mk_iff] class IsAbsolutelySimple : Prop where
  absolutelySimple : ∀ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
    IsSimpleModule (k' ⊗[k] A) (k' ⊗[k] M) -/
