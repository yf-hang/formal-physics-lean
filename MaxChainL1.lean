import Mathlib

namespace TwoSiteBoolean

/-
For l = 1, there are l + 1 = 2 internal energies.
We label them by Fin 2, namely 0 and 1.
Think of them as Y1 and Y2.
-/

abbrev Y := Fin 2

def y1 : Y := 0
def y2 : Y := 1

def S1 : Finset Y := {y1}
def S2 : Finset Y := {y2}
def Ytot : Finset Y := {y1, y2}

/-
Möbius sign on a Boolean lattice:
μ(∅, S) = (-1)^{|S|}.
-/
def mobius (S : Finset Y) : ℤ :=
  (-1 : ℤ) ^ S.card

example : mobius (∅ : Finset Y) = 1 := by
  simp [mobius]

example : mobius S1 = -1 := by
  simp [mobius, S1, y1]

example : mobius S2 = -1 := by
  simp [mobius, S2, y2]

example : mobius Ytot = 1 := by
  simp [mobius, Ytot, y1, y2]

/-
This is the ℓ = 1 Boolean expansion:

full Boolean lattice:
  F(∅) - F({Y1}) - F({Y2}) + F({Y1,Y2})

If your physics formula excludes the full subset YY,
then only the first three terms remain:
  F(∅) - F({Y1}) - F({Y2})
-/

section Expansion

variable (F : Finset Y → ℤ)

example :
    F ∅ - F S1 - F S2 + F Ytot
      =
    F ∅ + mobius S1 * F S1 + mobius S2 * F S2 + mobius Ytot * F Ytot := by
  simp [mobius, S1, S2, Ytot, y1, y2]
  ring

example :
    F ∅ - F S1 - F S2
      =
    F ∅ + mobius S1 * F S1 + mobius S2 * F S2 := by
  simp [mobius, S1, S2, y1, y2]
  ring

end Expansion

end TwoSiteBoolean
