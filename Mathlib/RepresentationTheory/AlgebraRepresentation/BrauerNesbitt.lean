/-
Copyright (c) 2026 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib
/-!
# Brauer-Nesbitt Theorem

This file collects various versions of the Brauer-Nesbitt theorem.

-/

variable {k A M N : Type*} [Field k] [Semiring A] [Algebra k A] [AddCommMonoid M]
  [AddCommMonoid N] []
