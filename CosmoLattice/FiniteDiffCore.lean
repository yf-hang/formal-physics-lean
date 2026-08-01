/-
Copyright (c) 2026 CosmoLattice contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CosmoLattice contributors
-/

import Mathlib

/-!
# Finite-difference core definitions

This module contains the definitions and algebraic helper lemmas used by the
finite-difference development. The general expansion theorem is kept in
`CosmoLattice.FiniteDiff` so it can be used as an independent AI proof target.
-/

namespace CosmoLattice.FiniteDiff

open scoped BigOperators

/-- Split the sum of a flattened list of pairs into the sums of both components. -/
lemma list_sum_flatMap_pair {α M : Type*} [AddCommMonoid M]
    (l : List α) (F G : α → M) :
    (l.flatMap (fun x => [F x, G x])).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [ih, add_assoc, add_left_comm]

/-- Pull pointwise negation through a list sum. -/
lemma list_sum_map_neg {α M : Type*} [AddCommGroup M]
    (l : List α) (F : α → M) :
    (l.map (fun x => -F x)).sum = - (l.map F).sum := by
  induction l with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [ih, add_comm]

/-- The one-step finite difference `Δ_h f(D) = f(D) - f(D + h)`. -/
def finiteDiff {A K : Type*} [Add A] [Sub K] (h : A) (f : A → K) : A → K :=
  fun D => f D - f (D + h)

/-- Ordered product of finite-difference operators over the list of shifts. -/
def iteratedFiniteDiff {A K : Type*} [Add A] [Sub K]
    (ys : List A) (f : A → K) : A → K :=
  ys.foldr (fun h g => finiteDiff h g) f

/-!
The alternating subset expansion for an arbitrary function `f`.
Here sublists of `ys` represent the subsets `V ⊆ \mathbf{Y}`.
-/
def finiteDiffExpansion {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) : K :=
  (ys.sublists.map fun V => (-1 : K) ^ V.length * f (D + V.sum)).sum

end CosmoLattice.FiniteDiff
