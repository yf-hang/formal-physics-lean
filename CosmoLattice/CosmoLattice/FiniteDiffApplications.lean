/-
Copyright (c) 2026 Y. Hang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Hang
-/

import CosmoLattice.FiniteDiff

/-!
# Applications of the finite-difference expansion

This file applies `iteratedFiniteDiff_eq_sum_subsets` to the inverse, sine, and
exponential functions. The general definitions and theorem remain in
`CosmoLattice.FiniteDiff`.
-/

namespace CosmoLattice.FiniteDiff

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

/--
Example 1: the finite-difference expansion for `f(D) = sin D`.
-/
theorem finiteDiff_sin_eq_sum_subsets
    (ys : List ℝ) (D : ℝ) :
    iteratedFiniteDiff ys (fun x : ℝ => Real.sin x) D =
      (ys.sublists.map fun V =>
        (-1 : ℝ) ^ V.length * Real.sin (D + V.sum)).sum := by
  rw [iteratedFiniteDiff_eq_sum_subsets]
  simp [finiteDiffExpansion]

/--
Example 2: the finite-difference expansion for `f(D) = e^D`.
-/
theorem finiteDiff_exp_eq_sum_subsets
    (ys : List ℝ) (D : ℝ) :
    iteratedFiniteDiff ys (fun x : ℝ => Real.exp x) D =
      (ys.sublists.map fun V =>
        (-1 : ℝ) ^ V.length * Real.exp (D + V.sum)).sum := by
  rw [iteratedFiniteDiff_eq_sum_subsets]
  simp [finiteDiffExpansion]

end CosmoLattice.FiniteDiff
