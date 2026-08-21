/-
Copyright (c) 2026 Y. Hang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Hang
-/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.Ring

/-!
# Finite-difference expansion

This file formalizes the general finite-difference expansion

  ∏ᵢ Δ_{yᵢ} f(D) = ∑_{V ⊆ \mathbf{Y}} (-1)^{|V|} f(D + ∑_{y ∈ V} y),

where Δ_y f(D) = f(D) - f(D + y).

The finite set \mathbf{Y} is represented by an ordered list `ys`.
Its sublists enumerate the subsets of \mathbf{Y},
with the inherited order used only to compute the sum of shifts.
-/

namespace CosmoLattice.FiniteDiff

lemma list_sum_flatMap_pair {α M : Type*} [AddCommMonoid M]
    (l : List α) (F G : α → M) :
    (l.flatMap (fun x => [F x, G x])).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [ih, add_assoc, add_left_comm]

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

/--
The alternating subset expansion for an arbitrary function `f`.
Here sublists of `ys` represent the subsets `V ⊆ \mathbf{Y}`.
-/
def finiteDiffExpansion {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) : K :=
  (ys.sublists.map fun V => (-1 : K) ^ V.length * f (D + V.sum)).sum

/--
General finite-difference identity:
`∏ᵢ Δ_{yᵢ} f(D) = ∑_{V ⊆ \mathbf{Y}} (-1)^|V| f(D + ∑_{y∈V} y)`.
-/
theorem iteratedFiniteDiff_eq_sum_subsets
    {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) :
    iteratedFiniteDiff ys f D = finiteDiffExpansion ys f D := by
  induction ys generalizing D with
  | nil =>
      simp [iteratedFiniteDiff, finiteDiffExpansion]
  | cons h ys ih =>
      simp only [iteratedFiniteDiff, List.foldr_cons, finiteDiff]
      change iteratedFiniteDiff ys f D - iteratedFiniteDiff ys f (D + h) =
        finiteDiffExpansion (h :: ys) f D
      rw [ih D, ih (D + h)]
      simp only [finiteDiffExpansion, List.sublists_cons]
      change
        (List.map (fun V => (-1 : K) ^ V.length * f (D + V.sum)) ys.sublists).sum -
          (List.map (fun V => (-1 : K) ^ V.length * f (D + h + V.sum))
            ys.sublists).sum =
        (List.map (fun V => (-1 : K) ^ V.length * f (D + V.sum))
          (ys.sublists.flatMap (fun V => [V, h :: V]))).sum
      rw [List.map_flatMap]
      simp only [List.map_cons, List.map_nil]
      rw [list_sum_flatMap_pair]
      simp only [List.length_cons, List.sum_cons, pow_succ]
      rw [show
        (List.map
            (fun V : List A => (-1 : K) ^ V.length * -1 * f (D + (h + V.sum)))
            ys.sublists).sum =
          - (List.map
              (fun V : List A => (-1 : K) ^ V.length * f (D + h + V.sum))
              ys.sublists).sum by
        rw [← list_sum_map_neg]
        congr with V
        simp [add_assoc]]
      ring

end CosmoLattice.FiniteDiff
