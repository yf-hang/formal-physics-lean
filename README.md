# TwoSiteBoolean

This project formalizes two equivalent descriptions of the finite-difference expansion used for two-site Boolean-lattice wavefunction coefficients.

## 1. Finite-Difference Expansion

This Lean file formalizes a standard alternating subset expansion for iterated finite differences.

The main identity is that applying a finite sequence of difference operators to a function `f` is equivalent to summing over all sublists, interpreted as subsets, with alternating signs:

$$
\prod_i \Delta_{y_i} f(D) = \sum_{S \subseteq \mathbf{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right)
$$

which is useful in the analysis of cosmology wavefunctions under loop level.

Here the one-step finite difference is defined by

$$
\Delta_h f(D) = f(D) - f(D + h)
$$

In the Lean development, the finite set $\mathbf{Y}$ is represented by an ordered list `ys`, and its subsets $S$ are represented by `ys.sublists`. The order inherited from the list is only used to compute the finite sum of shifts.

### Main Definitions

#### One-step finite difference

```lean
def finiteDiff {A K : Type*} [Add A] [Sub K] (h : A) (f : A -> K) : A -> K :=
  fun D => f D - f (D + h)
```

This represents the finite-difference operator:

$$
\Delta_h f(D) = f(D) - f(D + h).
$$

#### Iterated finite difference

```lean
def iteratedFiniteDiff {A K : Type*} [Add A] [Sub K]
    (ys : List A) (f : A -> K) : A -> K :=
  ys.foldr (fun h g => finiteDiff h g) f
```

For a list `ys = [y1, y2, ..., yn]`, this corresponds to

$$
\Delta_{y_1} \Delta_{y_2} \cdots \Delta_{y_n} f
$$

#### Alternating subset expansion

```lean
def finiteDiffExpansion {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A -> K) (D : A) : K :=
  (ys.sublists.map fun S => (-1 : K) ^ S.length * f (D + S.sum)).sum
```

This is the rhs of the expansion:

$$
\sum_{S \subseteq \mathbf{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right)
$$

### Main Theorem

The central theorem proves the general finite-difference identity:

```lean
theorem iteratedFiniteDiff_eq_sum_subsets
    {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A -> K) (D : A) :
    iteratedFiniteDiff ys f D = finiteDiffExpansion ys f D
```

In mathematical notation:

$$
\prod_i \Delta_{y_i} f(D)
  = \sum_{S \subseteq \mathbf{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right)
$$

### Proof Idea

We prove the identity

$$
\mathrm{iteratedFiniteDiff}\; ys\; f\; D  = \mathrm{finiteDiffExpansion}\; ys\; f\; D
$$

by induction on the list `ys`. In mathematical notation, this is the statement

$$
\prod_i \Delta_{y_i} f(D) = \sum_{S \subseteq \mathbf{Y}} (-1)^{|S|} f \left(D+\sum_{y\in S}y\right)
$$

where the sum is over the sublists of `ys`. These sublists play the role of subsets of the finite set of shifts.

For the empty list, there are no finite-difference operators. Hence the left-hand side is simply `f D`. On the right-hand side, the only sublist of `[]` is `[]` itself, whose length and sum are both zero. Therefore the subset expansion reduces to

$$
(-1)^0 f(D+0)=f(D)
$$

This is the base case of the induction and is discharged in Lean by simplifying the definitions of `iteratedFiniteDiff` and `finiteDiffExpansion`.

For the inductive step, write the list as `h :: ys`. The induction hypothesis says that the identity already holds for the shorter list `ys`. In Lean, the induction is performed with `generalizing D`, so the induction hypothesis is available for any argument, not only for the original `D`. This is important because the proof needs to use the hypothesis both at `D` and at `D+h`.

By the definition of `iteratedFiniteDiff`, applying the first finite-difference operator gives

$$
\mathrm{iteratedFiniteDiff} ys f D - \mathrm{iteratedFiniteDiff} ys f (D+h)
$$

The induction hypothesis is then applied to both terms. In Lean this is the step

```lean
rw [ih D, ih (D + h)]
```

which rewrites the two terms as subset expansions over the shorter list `ys`:

$$
\sum_{S \in ys.\mathrm{sublists}} (-1)^{|S|} f \left(D+\sum_{y\in S}y\right)
    - \sum_{S \in ys.\mathrm{sublists}} (-1)^{|S|} f \left(D+h+\sum_{y\in S}y\right)
$$

It remains to compare this expression with the subset expansion for the longer list `h :: ys`. Every sublist of `h :: ys` is obtained in exactly one of two ways: either the initial element `h` is not selected, in which case the sublist is a sublist `S` of `ys`; or the initial element `h` is selected, in which case the sublist has the form `h :: S`, where `S` is a sublist of `ys`. This is precisely the decomposition implemented by

```lean
List.sublists_cons
```

Equivalently, Lean rewrites the sublists of `h :: ys` as

```lean
ys.sublists.flatMap (fun S => [S, h :: S])
```

This expresses the fact that, for every sublist `S` of `ys`, there are two corresponding sublists of `h :: ys`:

```lean
S
h :: S
```

For each sublist `S` of `ys`, the sublist `S` itself contributes the term

$$
(-1)^{|S|} f \left(D+\sum_{y\in S}y\right)
$$

The corresponding sublist `h :: S` has length `|S|+1` and sum

$$
h+\sum_{y\in S}y
$$

Hence it contributes

$$
(-1)^{|S|+1} f\left(D+h+\sum_{y\in S}y\right) 
    = - (-1)^{|S|} f\left(D+h+\sum_{y\in S}y\right)
$$

Thus the expansion over all sublists of `h :: ys` becomes

$$
\sum_{S \in ys.\mathrm{sublists}} (-1)^{|S|} f\left(D+\sum_{y\in S}y\right) 
    - \sum_{S \in ys.\mathrm{sublists}} (-1)^{|S|} f \left(D+h+\sum_{y\in S}y\right)
$$

which is exactly the expression obtained from the induction hypothesis. This proves the inductive step.

The auxiliary lemmas are used only to reorganize the list sums appearing in this comparison. The lemma `list_sum_flatMap_pair` separates the two contributions produced by `flatMap`, corresponding to the two choices `S` and `h :: S`. The lemma `list_sum_map_neg` rewrites a sum of negated terms as the negative of a sum, allowing the contribution with the extra factor of `-1` to be written as the second subtractive term.

### Specialization to `1 / D`

The file then specializes the general identity to the function:

$$
f(D) = \frac{1}{D}
$$

The shifted denominator is defined as

```lean
def shiftedD {K : Type*} [Add K] [Zero K] (D : K) (S : List K) : K :=
  D + S.sum
```

This represents

$$
D_S = D + \sum_{y \in S} y
$$

The final theorem is

```lean
theorem finiteDiff_inv_eq_sum_subsets
    {K : Type*} [Field K] (ys : List K) (D : K) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      (ys.sublists.map fun S => (-1 : K) ^ S.length / shiftedD D S).sum
```

Mathematically, this is

$$
\prod_i \Delta_{y_i} \left(\frac{1}{D}\right)
  = \sum_{S \subseteq \mathbf{Y}} \frac{(-1)^{|S|}}{D_S}
$$

where

$$
D_S = D + \sum_{y \in S} y
$$

### Notes

- Sublists of `ys` are used as the Lean representation of subsets.
- The ordering of `ys` only matters for producing concrete lists and sums; the final formula is the usual subset expansion.

## 2. Maximal-Chain Expansion

The file `TwoSiteBoolean/MaxChain.lean` proves the maximal-chain form of the same finite-difference product.

Mathematically, the identity is

$$
\prod_i \Delta_{y_i}\left(\frac{1}{D}\right) = \left(\prod_i y_i\right)\sum_{\pi} \prod_{r} \frac{1}{D+\sigma[\pi]_r}
$$

where $\pi$ ranges over all orderings of the shifts, and

$$
\sigma[\pi]_r = y_{\pi_1}+\cdots+y_{\pi_r} \qquad \sigma[\pi]_0 = 0
$$

Each ordering $\pi$ specifies one maximal chain in the Boolean lattice:

$$
\varnothing \subset \{y_{\pi_1}\} \subset \{y_{\pi_1},y_{\pi_2}\} \subset \cdots \subset \mathbf{Y}
$$

### Chain Product

The product over the shifted denominators along one maximal chain is represented recursively by:

```lean
def chainProduct {K : Type*} [Field K] (D : K) : List K -> K
  | [] => 1 / D
  | y :: ys => (1 / D) * chainProduct (D + y) ys
```

For `ys = [y1, y2, ..., yn]`, this represents

$$
\frac{1}{D} \frac{1}{D+y_1} \frac{1}{D+y_1+y_2} \cdots \frac{1}{D+y_1+\cdots+y_n}
$$

### Sum Over Maximal Chains

The maximal-chain side is the sum of `chainProduct` over all permutations of the list of shifts:

```lean
def maxChainSum {K : Type*} [Field K] (D : K) (ys : List K) : K :=
  (ys.permutations'.map (chainProduct D)).sum
```

Here `ys.permutations'` is Lean's list of all orderings of `ys`. Thus it plays the role of the sum over $\pi \in S_n$.

### Nonzero Denominator Conditions

Since this proof uses `field_simp`, the Lean statement includes explicit nonzero-denominator assumptions.

```lean
def chainDenomsNonzero {K : Type*} [Field K] : K -> List K -> Prop
  | D, [] => D ≠ 0
  | D, y :: ys => D ≠ 0 ∧ chainDenomsNonzero (D + y) ys
```

The final theorem uses a recursive sufficient condition:

```lean
def maxChainDenomsNonzero {K : Type*} [Field K] : K -> List K -> Prop
  | D, [] => D ≠ 0
  | D, y :: ys =>
      maxChainDenomsNonzero D ys ∧
        maxChainDenomsNonzero (D + y) ys ∧
          ∀ p ∈ ys.permutations',
            chainDenomsNonzero D p ∧ chainDenomsNonzero (D + y) p
```

This condition says that all denominators needed by the induction and by the maximal-chain summands are nonzero.

### Telescoping Lemma

The key algebraic step is the Lean theorem:

```lean
private theorem chainProduct_sub_shift_eq
    {K : Type*} [Field K] (D h : K) (ys : List K)
    (hD : chainDenomsNonzero D ys)
    (hDh : chainDenomsNonzero (D + h) ys) :
    chainProduct D ys - chainProduct (D + h) ys =
      h * ((List.permutations'Aux h ys).map (chainProduct D)).sum
```

This is the Lean version of the telescoping lemma in the algebraic proof. In mathematical notation:

$$
\prod_{r=0}^{M}\frac{1}{D+\sigma_r} - \prod_{r=0}^{M}\frac{1}{D+h+\sigma_r} = h\sum_{j=0}^{M} \left(\prod_{r=0}^{j}\frac{1}{D+\sigma_r}\right) \left(\prod_{r=j}^{M}\frac{1}{D+h+\sigma_r}\right).
$$

The right-hand side inserts the new shift `h` into every possible position of the chain. In Lean this insertion is encoded by:

```lean
List.permutations'Aux h ys
```

### Summed Telescoping Step

The next private theorem applies the telescoping lemma to every existing chain:

```lean
private theorem sum_chainProduct_sub_shift_eq
    {K : Type*} [Field K] (D h : K) (ps : List (List K))
    (hps : ∀ p ∈ ps, chainDenomsNonzero D p ∧ chainDenomsNonzero (D + h) p) :
    (ps.map (chainProduct D)).sum - (ps.map (chainProduct (D + h))).sum =
      h * ((ps.flatMap (List.permutations'Aux h)).map (chainProduct D)).sum
```

This expresses the induction step at the level of all chains: applying one more finite difference inserts the new shift into every possible position of every old maximal chain.

### Main Theorem

The general maximal-chain formula is:

```lean
theorem iteratedFiniteDiff_inv_eq_prod_maxChainSum
    {K : Type*} [Field K] (ys : List K) (D : K)
    (hden : maxChainDenomsNonzero D ys) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      ys.prod * maxChainSum D ys
```

Mathematically:

$$
\prod_i \Delta_{y_i}\left(\frac{1}{D}\right) = \left(\prod_i y_i\right) \sum_{\pi} \prod_r \frac{1}{D+\sigma[\pi]_r}
$$

### Proof Idea

The proof is by induction on the list `ys`.

For the empty list, both sides reduce to $1/D$.

For the inductive step, write the list as `y :: ys`. By definition of finite difference,

$$
\Delta_y F(D) = F(D) - F(D+y)
$$

Using the induction hypothesis at both $D$ and $D+y$, the left-hand side becomes

$$
\left(\prod_{z \in ys} z\right) \left(\mathrm{maxChainSum}(D,ys) - \mathrm{maxChainSum}(D+y,ys) \right)
$$

The summed telescoping lemma rewrites the difference of the two maximal-chain sums as

$$
y\sum_{\text{all insertions of }y}\prod_r \frac{1}{D+\sigma_r}
$$

Multiplying by the old product $\prod_{z \in ys} z$ gives the new product

$$
y\prod_{z \in ys} z
$$

The inserted chains are exactly the permutations of `y :: ys`, since every ordering of the longer list is obtained by inserting `y` into one ordering of `ys`. This completes the induction.

### Existing Examples

The old explicit examples are still present in `MaxChain.lean`:

- `bubble.fin_diff_identity_bubble` proves the two-shift case.
- `sunset.fin_diff_identity_sunset` proves the three-shift case.

The new theorem `iteratedFiniteDiff_inv_eq_prod_maxChainSum` proves the same identity for an arbitrary list of shifts.
