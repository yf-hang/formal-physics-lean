/-
Copyright (c) 2026 Y. Hang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Hang
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!

# Abstract gravitational equivalence theorem

This file provides a small asymptotic interface for gravitational
equivalence theorems.

Suppose an exact equivalence-theorem identity has the form

  A(E) = C * B(E) + R(E),

where

* `A` is the physical graviton amplitude,
* `B` is the corresponding Goldstone amplitude,
* `C` is the modification factor,
* `R` is the residual contribution.

If the leading Goldstone amplitude has energy power `E^p`, and the
residual is suppressed by at least one factor of `M / E`, then

  R(E) = O(M * E^(p - 1)).

Consequently,

  A(E) - C * B(E) = O(M * E^(p - 1))

and therefore

  A(E) - C * B(E) = o(E^p).

For the warped gravitational equivalence theorems of
arXiv:2406.12713, the generalized Goldstone power counting is

  p = 2 * (L + 1)

at loop order `L`.

The derivation of the exact GRET identity and of the `M / E`
suppression from BRST identities and external-state analysis is
treated as analytic input to this interface.

-/

@[expose] public section

open Filter
open Asymptotics

namespace GRET

/-! ## Basic definitions -/

/--
A scattering amplitude viewed as a complex-valued function of the
high-energy scale `E`.
-/
abbrev Amplitude := Real → Complex

/--
A real-valued profile used for asymptotic energy power counting.
-/
abbrev EnergyProfile := Real → Real

/--
The leading energy profile `E^p`.
-/
def leadingPowerProfile (p : Nat) : EnergyProfile :=
  fun E => E ^ p

/--
The energy profile of a contribution suppressed by one factor of
`M / E` relative to a leading `E^p` amplitude:

  (M / E) * E^p = M * E^(p - 1).

The intended use is for `p > 0`.
-/
def residualPowerProfile
    (massScale : Real)
    (p : Nat) : EnergyProfile :=
  fun E => massScale * E ^ (p - 1)

/--
The leading Goldstone energy power occurring in the generalized
power counting of the warped GRET at loop order `L`:

  p = 2 * (L + 1).
-/
def gretLeadingPower (loopOrder : Nat) : Nat :=
  2 * (loopOrder + 1)

/--
The warped-GRET leading power is always positive.
-/
theorem gretLeadingPower_pos (loopOrder : Nat) :
    0 < gretLeadingPower loopOrder := by
  simp [gretLeadingPower]


/-! ## General equivalence-theorem statement -/

/--
An abstract equivalence-theorem statement with high-energy power counting.

The exact identity is

  lhs = modification * rhs + residual.

If the leading Goldstone amplitude has energy power `E^p`, the residual
is assumed to obey the GRET suppression

  residual = O(M * E^(p - 1)).

This expresses the paper's statement that the residual is suppressed
by at least one factor of `M / E` relative to the leading Goldstone
amplitude.
-/
structure Statement where

  /-- Physical-particle amplitude. -/
  lhs : Amplitude

  /-- Corresponding Goldstone amplitude. -/
  rhs : Amplitude

  /-- Multiplicative modification factor. -/
  modification : Complex

  /-- Residual contribution. -/
  residual : Amplitude

  /-- Mass scale entering the `M / E` suppression. -/
  massScale : Real

  /-- Leading energy power `p` of the corresponding Goldstone amplitude. -/
  leadingPower : Nat

  /-- The leading power is positive. -/
  leadingPower_pos : 0 < leadingPower

  /--
  Exact equivalence-theorem identity.
  -/
  identity :
    ∀ E,
      lhs E =
        modification * rhs E + residual E

  /--
  The residual is suppressed by at least one power of `M / E`
  relative to the leading `E^p` Goldstone behavior.
  -/
  residual_isBigO :
    residual =O[atTop]
      residualPowerProfile massScale leadingPower


/-! ## Power-counting lemmas -/

/--
For every fixed mass scale `M` and positive power `p`,

  M * E^(p - 1) = o(E^p)

as `E → ∞`.
-/
theorem residualPowerProfile_isLittleO
    (massScale : Real)
    (p : Nat)
    (hp : 0 < p) :
    residualPowerProfile massScale p
      =o[atTop]
        leadingPowerProfile p := by
  have hpow :
      (fun E : Real => E ^ (p - 1))
        =o[atTop]
      (fun E : Real => E ^ p) := by
    apply Asymptotics.isLittleO_pow_pow_atTop_of_lt
    exact Nat.sub_lt hp (by simp)
  rw [← Asymptotics.isLittleO_norm_norm]
  simpa [residualPowerProfile, leadingPowerProfile, norm_mul, norm_pow] using
    hpow.norm_norm.const_mul_left ‖massScale‖


/-! ## Main results -/

/--
The difference between the physical amplitude and the modified
Goldstone amplitude has the same `M / E`-suppressed energy bound
as the residual:

  lhs - C * rhs = O(M * E^(p - 1)).
-/
theorem Statement.equivalence_isBigO
    (g : Statement) :
    (fun E =>
      g.lhs E -
        g.modification * g.rhs E)
      =O[atTop]
        residualPowerProfile
          g.massScale
          g.leadingPower := by
  have hDifference :
      (fun E =>
        g.lhs E -
          g.modification * g.rhs E)
        =
      g.residual := by
    funext E
    rw [g.identity E]
    simp
  rw [hDifference]
  exact g.residual_isBigO

/--
The physical amplitude and the modified Goldstone amplitude agree
at leading energy power `E^p`:

  lhs - C * rhs = o(E^p).

This is the leading-order high-energy content of the equivalence theorem.
-/
theorem Statement.equivalence_isLittleO
    (g : Statement) :
    (fun E =>
      g.lhs E -
        g.modification * g.rhs E)
      =o[atTop]
        leadingPowerProfile g.leadingPower := by
  exact g.equivalence_isBigO.trans_isLittleO
    (residualPowerProfile_isLittleO
      g.massScale
      g.leadingPower
      g.leadingPower_pos)

/--
Specialization to the case in which the modification factor is one.

Whenever `modification = 1`,

  lhs - rhs = o(E^p).
-/
theorem Statement.equivalence_isLittleO_of_modification_eq_one
    (g : Statement)
    (hmod : g.modification = 1) :
    (fun E =>
      g.lhs E - g.rhs E)
      =o[atTop]
        leadingPowerProfile g.leadingPower := by
  simpa [hmod] using g.equivalence_isLittleO

end GRET
