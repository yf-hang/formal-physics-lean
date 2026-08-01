/-
Copyright (c) 2026 CosmoLattice contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CosmoLattice contributors
-/

import CosmoLattice.FiniteDiffCore

/-!
# AI proof completion demo

This file is generated from `AI_Proof_Demo/PartialProof.lean.template` by
`AI_Proof_Demo/ollama_prove.py`. The script asks a local Ollama model for the proof
hole below and writes this file only after Lean accepts the completed theorem.
-/

namespace AIProofDemo

open CosmoLattice.FiniteDiff

theorem iteratedFiniteDiff_eq_sum_subsets_ai_completion
    {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) :
    CosmoLattice.FiniteDiff.iteratedFiniteDiff ys f D =
      CosmoLattice.FiniteDiff.finiteDiffExpansion ys f D := by
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

end AIProofDemo
