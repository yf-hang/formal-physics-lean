# TwoSiteBoolean

This Lean project formalizes the `l = 1` case of a two-site Boolean
expansion.

The main file is:

```text
TwoSiteBoolean/MaxChainL1.lean
```

## Verified Content

For `l = 1`, the internal-energy labels are represented by:

```lean
abbrev Y := Fin 2
```

with distinguished elements:

```lean
y1 : Y
y2 : Y
```

and Boolean subsets:

```lean
S1   = {y1}
S2   = {y2}
Ytot = {y1, y2}
```

The file verifies the Boolean-lattice Mobius sign

```text
mobius(S) = (-1) ^ card(S)
```

for the empty set, the two singleton subsets, and the total subset.

It also verifies the full `l = 1` Boolean expansion:

```text
F(empty) - F(S1) - F(S2) + F(Ytot)
=
F(empty)
  + mobius(S1) * F(S1)
  + mobius(S2) * F(S2)
  + mobius(Ytot) * F(Ytot)
```

and the proper-subset version excluding `Ytot`:

```text
F(empty) - F(S1) - F(S2)
=
F(empty) + mobius(S1) * F(S1) + mobius(S2) * F(S2)
```

## Shifted Divisor

The shifted diagonal divisor is encoded as:

```lean
def Dshift (D : ℤ) (energy : Y → ℤ) (S : Finset Y) : ℤ :=
  D + 2 * (∑ i ∈ S, energy i)
```

The file verifies the four `l = 1` cases:

```text
D_empty = D
D_S1    = D + 2 * energy(y1)
D_S2    = D + 2 * energy(y2)
D_Ytot  = D + 2 * (energy(y1) + energy(y2))
```

## Shifted Expansion

For an arbitrary function `G : ℤ → ℤ`, the shifted term is:

```text
shiftedTerm(D, energy, G, S) = mobius(S) * G(Dshift(D, energy, S))
```

The file verifies both:

```text
G(D)
  - G(D + 2 * energy(y1))
  - G(D + 2 * energy(y2))
  + G(D + 2 * (energy(y1) + energy(y2)))
```

and the proper-subset version:

```text
G(D)
  - G(D + 2 * energy(y1))
  - G(D + 2 * energy(y2))
```

## Indexed Proper Subsets

The paper-style indexing of proper subsets is encoded by:

```text
S_0 = {Y1}
S_1 = {Y2}
S_2 = empty
```

as a function:

```lean
properSubsetL1 : Fin 3 → Finset Y
```

The indexed shifted sum is:

```lean
properShiftedSumL1
    (D : ℤ) (energy : Y → ℤ) (G : ℤ → ℤ) : ℤ
```

and the file verifies:

```text
properShiftedSumL1(D, energy, G)
=
- G(D + 2 * energy(y1))
  - G(D + 2 * energy(y2))
  + G(D)
```

equivalently:

```text
properShiftedSumL1(D, energy, G)
=
G(D)
  - G(D + 2 * energy(y1))
  - G(D + 2 * energy(y2))
```

## Checking

Run:

```bash
lake build
```

The project currently builds successfully with Lean `v4.30.0-rc2`.
