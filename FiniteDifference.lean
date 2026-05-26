import Mathlib

namespace TwoSiteBoolean

open scoped BigOperators

/-
This file formalizes the finite-difference expansion

  ∏ᵢ Δ_{yᵢ} (1 / D) = ∑_{S ⊆ \mathbf{Y}} (-1) ^ |S| / D_S,

where Δ_y f(D) = f(D) - f(D + y) and D_S = D + ∑_{y ∈ S} y.

The finite set \mathbf{Y} is represented by an ordered list `ys`.  Its sublists
enumerate the subsets of \mathbf{Y}, with the inherited order used only to compute
the sum of shifts.
-/

private lemma list_sum_flatMap_pair {α M : Type*} [AddCommMonoid M]
    (l : List α) (F G : α → M) :
    (l.flatMap (fun x => [F x, G x])).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [ih, add_assoc, add_left_comm]

private lemma list_sum_map_neg {α M : Type*} [AddCommGroup M]
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
Here sublists of `ys` represent the subsets `S ⊆ \mathbf{Y}`.
-/
def finiteDiffExpansion {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) : K :=
  (ys.sublists.map fun S => (-1 : K) ^ S.length * f (D + S.sum)).sum

/--
General finite-difference identity:
`∏ᵢ Δ_{yᵢ} f(D) = ∑_{S ⊆ \mathbf{Y}} (-1)^|S| f(D + ∑_{y∈S} y)`.
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
        (List.map (fun S => (-1 : K) ^ S.length * f (D + S.sum)) ys.sublists).sum -
          (List.map (fun S => (-1 : K) ^ S.length * f (D + h + S.sum))
            ys.sublists).sum =
        (List.map (fun S => (-1 : K) ^ S.length * f (D + S.sum))
          (ys.sublists.flatMap (fun S => [S, h :: S]))).sum
      rw [List.map_flatMap]
      simp only [List.map_cons, List.map_nil]
      rw [list_sum_flatMap_pair]
      simp only [List.length_cons, List.sum_cons, pow_succ]
      rw [show
        (List.map
            (fun S : List A => (-1 : K) ^ S.length * -1 * f (D + (h + S.sum)))
            ys.sublists).sum =
          - (List.map
              (fun S : List A => (-1 : K) ^ S.length * f (D + h + S.sum))
              ys.sublists).sum by
        rw [← list_sum_map_neg]
        congr with S
        simp [add_assoc]]
      ring

/-- The shifted denominator `D_S = D + ∑_{y∈S} y`. -/
def shiftedD {K : Type*} [Add K] [Zero K] (D : K) (S : List K) : K :=
  D + S.sum

/--
Application of the finite-difference expansion to the function `f(D) = 1 / D`, yielding

`∏ᵢ Δ_{yᵢ} (1 / D) = ∑_{S ⊆ \mathbf{Y}} (-1)^|S| / D_S`.

In this Lean statement, `ys.sublists` enumerates the subsets `S ⊆ Y`.
-/
theorem finiteDiff_inv_eq_sum_subsets
    {K : Type*} [Field K] (ys : List K) (D : K) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      (ys.sublists.map fun S => (-1 : K) ^ S.length / shiftedD D S).sum := by
  rw [iteratedFiniteDiff_eq_sum_subsets]
  simp [finiteDiffExpansion, shiftedD, div_eq_mul_inv]

end TwoSiteBoolean
