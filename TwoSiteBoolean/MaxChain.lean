import Mathlib
import TwoSiteBoolean.FiniteDifference

namespace TwoSiteBoolean

/--
Product of shifted denominators along one maximal chain.

For a chain ordered by `ys = [y₁, ..., yₙ]`, this is

`1 / D * 1 / (D + y₁) * ... * 1 / (D + y₁ + ... + yₙ)`.
-/
def chainProduct {K : Type*} [Field K] (D : K) : List K → K
  | [] => 1 / D
  | y :: ys => (1 / D) * chainProduct (D + y) ys

/-- The maximal-chain side, summed over all orderings of `ys`. -/
def maxChainSum {K : Type*} [Field K] (D : K) (ys : List K) : K :=
  (ys.permutations'.map (chainProduct D)).sum

/-- Nonvanishing of every denominator appearing in `chainProduct D ys`. -/
def chainDenomsNonzero {K : Type*} [Field K] : K → List K → Prop
  | D, [] => D ≠ 0
  | D, y :: ys => D ≠ 0 ∧ chainDenomsNonzero (D + y) ys

/--
A recursive sufficient nonzero condition for the maximal-chain proof.

For `y :: ys`, the proof applies the induction hypothesis at `D` and at
`D + y`, and applies the telescoping lemma to each ordering of `ys`.
-/
def maxChainDenomsNonzero {K : Type*} [Field K] : K → List K → Prop
  | D, [] => D ≠ 0
  | D, y :: ys =>
      maxChainDenomsNonzero D ys ∧
        maxChainDenomsNonzero (D + y) ys ∧
          ∀ p ∈ ys.permutations',
            chainDenomsNonzero D p ∧ chainDenomsNonzero (D + y) p

private theorem chainProduct_sub_shift_eq
    {K : Type*} [Field K] (D h : K) (ys : List K)
    (hD : chainDenomsNonzero D ys)
    (hDh : chainDenomsNonzero (D + h) ys) :
    chainProduct D ys - chainProduct (D + h) ys =
      h * ((List.permutations'Aux h ys).map (chainProduct D)).sum := by
  induction ys generalizing D with
  | nil =>
      simp [chainProduct, chainDenomsNonzero] at hD hDh ⊢
      field_simp [hD, hDh]
      ring
  | cons y ys ih =>
      have hD0 : D ≠ 0 := hD.1
      have hDy : chainDenomsNonzero (D + y) ys := hD.2
      have hDh0 : D + h ≠ 0 := hDh.1
      have hDhy : chainDenomsNonzero (D + y + h) ys := by
        simpa [add_assoc, add_left_comm, add_comm] using hDh.2
      have ih' := ih (D + y) hDy hDhy
      have hshift :
          chainProduct (D + y + h) ys = chainProduct (D + h + y) ys := by
        congr 1
        ring
      rw [hshift] at ih'
      have hsum :
          (List.map (chainProduct D ∘ List.cons y) (List.permutations'Aux h ys)).sum =
            (1 / D) * (List.map (chainProduct (D + y)) (List.permutations'Aux h ys)).sum := by
        simpa [Function.comp_def, chainProduct] using
          List.sum_map_mul_left (List.permutations'Aux h ys) (chainProduct (D + y)) (1 / D)
      have hAB :
          chainProduct (D + y) ys =
            chainProduct (D + h + y) ys +
              h * (List.map (chainProduct (D + y)) (List.permutations'Aux h ys)).sum := by
        rw [sub_eq_iff_eq_add] at ih'
        simpa [add_comm] using ih'
      simp only [chainProduct, List.permutations'Aux, List.map_cons, List.map_map, List.sum_cons]
      rw [hsum]
      field_simp [hD0, hDh0]
      rw [hAB]
      ring

private theorem sum_chainProduct_sub_shift_eq
    {K : Type*} [Field K] (D h : K) (ps : List (List K))
    (hps : ∀ p ∈ ps, chainDenomsNonzero D p ∧ chainDenomsNonzero (D + h) p) :
    (ps.map (chainProduct D)).sum - (ps.map (chainProduct (D + h))).sum =
      h * ((ps.flatMap (List.permutations'Aux h)).map (chainProduct D)).sum := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      have hp : chainDenomsNonzero D p ∧ chainDenomsNonzero (D + h) p := hps p (by simp)
      have hps' : ∀ q ∈ ps, chainDenomsNonzero D q ∧ chainDenomsNonzero (D + h) q := by
        intro q hq
        exact hps q (by simp [hq])
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
      rw [List.map_append, List.sum_append]
      have hpEq := chainProduct_sub_shift_eq D h p hp.1 hp.2
      have hpsEq := ih hps'
      have hpEq' :
          chainProduct D p =
            chainProduct (D + h) p +
              h * (List.map (chainProduct D) (List.permutations'Aux h p)).sum := by
        rw [sub_eq_iff_eq_add] at hpEq
        simpa [add_comm] using hpEq
      have hpsEq' :
          (List.map (chainProduct D) ps).sum =
            (List.map (chainProduct (D + h)) ps).sum +
              h * (List.map (chainProduct D) (List.flatMap (List.permutations'Aux h) ps)).sum := by
        rw [sub_eq_iff_eq_add] at hpsEq
        simpa [add_comm] using hpsEq
      rw [hpEq', hpsEq']
      ring

/--
General maximal-chain formula for an arbitrary list of shifts.

This is the Lean version of equation `fin-diff-sum-max-chain`:

`∏ᵢ Δ_{yᵢ} (1 / D) =
  (∏ᵢ yᵢ) ∑_{π} ∏_{r} 1 / (D + σ[π]_r)`.

The list `ys.permutations'` enumerates the orderings `π`, and `chainProduct`
is the product over cumulative sums along the corresponding maximal chain.
-/
theorem iteratedFiniteDiff_inv_eq_prod_maxChainSum
    {K : Type*} [Field K] (ys : List K) (D : K)
    (hden : maxChainDenomsNonzero D ys) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      ys.prod * maxChainSum D ys := by
  induction ys generalizing D with
  | nil =>
      simp [iteratedFiniteDiff, maxChainSum, chainProduct, maxChainDenomsNonzero] at hden ⊢
  | cons y ys ih =>
      have hdenD : maxChainDenomsNonzero D ys := hden.1
      have hdenDy : maxChainDenomsNonzero (D + y) ys := hden.2.1
      have hchain :
          ∀ p ∈ ys.permutations',
            chainDenomsNonzero D p ∧ chainDenomsNonzero (D + y) p := hden.2.2
      simp only [iteratedFiniteDiff, List.foldr_cons, finiteDiff]
      change iteratedFiniteDiff ys (fun x : K => 1 / x) D -
          iteratedFiniteDiff ys (fun x : K => 1 / x) (D + y) =
        (y :: ys).prod * maxChainSum D (y :: ys)
      rw [ih D hdenD, ih (D + y) hdenDy]
      simp only [maxChainSum, List.permutations']
      rw [← mul_sub]
      rw [sum_chainProduct_sub_shift_eq D y ys.permutations' hchain]
      simp [List.prod_cons]
      ring

namespace bubble

def D0 (D : ℚ) : ℚ := D
def D1 (D e1 : ℚ) : ℚ := D + e1
def D2 (D e2 : ℚ) : ℚ := D + e2
def D3 (D e1 e2 : ℚ) : ℚ := D + e1 + e2

theorem fin_diff_identity_bubble
    (D e1 e2 : ℚ)
    (h0 : D0 D ≠ 0)
    (h1 : D1 D e1 ≠ 0)
    (h2 : D2 D e2 ≠ 0)
    (h12 : D3 D e1 e2 ≠ 0) :
    1 / D0 D
      - 1 / D1 D e1
      - 1 / D2 D e2
      + 1 / D3 D e1 e2
    =
    e1 * e2 *
      (1 / (D0 D * D1 D e1 * D3 D e1 e2)
       + 1 / (D0 D * D2 D e2 * D3 D e1 e2)) := by
  simp [D0, D1, D2, D3] at h0 h1 h2 h12 ⊢
  field_simp [h0, h1, h2, h12]
  ring

end bubble


namespace sunset

def D0 (D : ℚ) : ℚ := D
def D1 (D e1 : ℚ) : ℚ := D + e1
def D2 (D e2 : ℚ) : ℚ := D + e2
def D3 (D e3 : ℚ) : ℚ := D + e3
def D4 (D e1 e2 : ℚ) : ℚ := D + e1 + e2
def D5 (D e1 e3 : ℚ) : ℚ := D + e1 + e3
def D6 (D e2 e3 : ℚ) : ℚ := D + e2 + e3
def D7 (D e1 e2 e3 : ℚ) : ℚ := D + e1 + e2 + e3

theorem fin_diff_identity_sunset
    (D e1 e2 e3 : ℚ)
    (h0 : D0 D ≠ 0)
    (h1 : D1 D e1 ≠ 0)
    (h2 : D2 D e2 ≠ 0)
    (h3 : D3 D e3 ≠ 0)
    (h4 : D4 D e1 e2 ≠ 0)
    (h5 : D5 D e1 e3 ≠ 0)
    (h6 : D6 D e2 e3 ≠ 0)
    (h7 : D7 D e1 e2 e3 ≠ 0) :
    1 / D0 D
      - 1 / D1 D e1
      - 1 / D2 D e2
      - 1 / D3 D e3
      + 1 / D4 D e1 e2
      + 1 / D5 D e1 e3
      + 1 / D6 D e2 e3
      - 1 / D7 D e1 e2 e3
    =
    e1 * e2 * e3 *
      (1 / (D0 D * D1 D e1 * D4 D e1 e2 * D7 D e1 e2 e3)
       + 1 / (D0 D * D1 D e1 * D5 D e1 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D2 D e2 * D4 D e1 e2 * D7 D e1 e2 e3)
       + 1 / (D0 D * D2 D e2 * D6 D e2 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D3 D e3 * D5 D e1 e3 * D7 D e1 e2 e3)
       + 1 / (D0 D * D3 D e3 * D6 D e2 e3 * D7 D e1 e2 e3)) := by
  simp [D0, D1, D2, D3, D4, D5, D6, D7] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  field_simp [h0, h1, h2, h3, h4, h5, h6, h7]
  ring

end sunset

end TwoSiteBoolean
