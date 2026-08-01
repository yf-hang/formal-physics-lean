/-
Copyright (c) 2026 CosmoLattice contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CosmoLattice contributors
-/

import CosmoLattice.FiniteDiffCore

/-!
# Finite-difference expansion

This file formalizes the finite-difference expansion

  ∏ᵢ Δ_{yᵢ} (1 / D) = ∑_{V ⊆ \mathbf{Y}} (-1)^{|V|} / D_V,

where Δ_y f(D) = f(D) - f(D + y) and D_V = D + ∑_{y ∈ V} y.

The finite set \mathbf{Y} is represented by an ordered list `ys`.
Its sublists enumerate the subsets of \mathbf{Y},
with the inherited order used only to compute the sum of shifts.
-/

namespace CosmoLattice.FiniteDiff

open scoped BigOperators

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

/-
The shifted denominator `D_V = D + ∑_{y∈V} y`.
-/
def shiftedD {K : Type*} [Add K] [Zero K] (D : K) (V : List K) : K :=
  D + V.sum

/--
Application of the finite-difference expansion to the function `f(D) = 1 / D`, yielding

`∏ᵢ Δ_{yᵢ} (1 / D) = ∑_{V ⊆ \mathbf{Y}} (-1)^{|V|} / D_V`.

In this Lean statement, `ys.sublists` enumerates the subsets `V ⊆ Y`.
-/
theorem finiteDiff_inv_eq_sum_subsets
    {K : Type*} [Field K] (ys : List K) (D : K) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      (ys.sublists.map fun V => (-1 : K) ^ V.length / shiftedD D V).sum := by
  rw [iteratedFiniteDiff_eq_sum_subsets]
  simp [finiteDiffExpansion, shiftedD, div_eq_mul_inv]

end CosmoLattice.FiniteDiff
