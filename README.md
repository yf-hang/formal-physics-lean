## Finite Difference Expansion

This Lean file formalizes a standard alternating subset expansion for iterated finite differences.

The main identity is that applying a finite sequence of difference operators to a function `f` is equivalent to summing over all sublists, interpreted as subsets, with alternating signs:

$$
\prod_i \Delta_{y_i} f(D) = \sum_{S \subseteq \boldsymbol{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right).
$$

Here the one-step finite difference is defined by

$$
\Delta_h f(D) = f(D) - f(D + h).
$$

In the Lean development, the finite set `Y` is represented by an ordered list `ys`, and its subsets are represented by `ys.sublists`. The order inherited from the list is only used to compute the finite sum of shifts.

## Main Definitions

### One-step finite difference

```lean
def finiteDiff {A K : Type*} [Add A] [Sub K] (h : A) (f : A -> K) : A -> K :=
  fun D => f D - f (D + h)
```

This represents the operator

$$
\Delta_h f(D) = f(D) - f(D + h).
$$

### Iterated finite difference

```lean
def iteratedFiniteDiff {A K : Type*} [Add A] [Sub K]
    (ys : List A) (f : A -> K) : A -> K :=
  ys.foldr (fun h g => finiteDiff h g) f
```

For a list `ys = [y1, y2, ..., yn]`, this corresponds to

$$
\Delta_{y_1} \Delta_{y_2} \cdots \Delta_{y_n} f.
$$

### Alternating subset expansion

```lean
def finiteDiffExpansion {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A -> K) (D : A) : K :=
  (ys.sublists.map fun S => (-1 : K) ^ S.length * f (D + S.sum)).sum
```

This is the right-hand side of the expansion:

$$
\sum_{S \subseteq \boldsymbol{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right).
$$

## Main Theorem

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
  = \sum_{S \subseteq \boldsymbol{Y}} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right).
$$

## Proof Idea

The proof proceeds by induction on the list `ys`.

For the empty list, there are no difference operators, so both sides reduce to `f D`.

For the inductive step, suppose the list is `h :: ys`. Applying the first finite difference gives

$$
\mathrm{iteratedFiniteDiff}(ys, f)(D) - \mathrm{iteratedFiniteDiff}(ys, f)(D + h)
$$

By the induction hypothesis, these two terms become two subset sums over `ys`:

$$
\sum_{S \subseteq ys} (-1)^{|S|} f\left(D + \sum_{y \in S} y\right) - \sum_{S \subseteq ys} (-1)^{|S|} f\left(D + h + \sum_{y \in S} y\right)
$$

On the other hand, every sublist of `h :: ys` is either:

1. a sublist `S` of `ys`, not containing `h`; or
2. a sublist `h :: S`, containing `h`.

The second case has one extra element, so its sign gains a factor of `-1`:

$$
(-1)^{|S| + 1} = -(-1)^{|S|}
$$

Thus the subset expansion over `h :: ys` matches exactly the difference of the two subset sums above.

The auxiliary lemmas about list sums are used to reorganize sums over lists produced by `flatMap` and to rewrite sums of negated terms.

## Specialization to `1 / D`

The file then specializes the general identity to the function

$$
f(x) = \frac{1}{x}.
$$

The shifted denominator is defined as

```lean
def shiftedD {K : Type*} [Add K] [Zero K] (D : K) (S : List K) : K :=
  D + S.sum
```

This represents

$$
D_S = D + \sum_{y \in S} y.
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
  = \sum_{S \subseteq \boldsymbol{Y}} \frac{(-1)^{|S|}}{D_S}.
$$

where

$$
D_S = D + \sum_{y \in S} y.
$$

## Examples

For $\boldsymbol{Y}=\{y_1,y_2\}$:
```math
\begin{aligned}
\prod_{i=1}^{2}\Delta_{y_i}\left[\frac{1}{D}\right]
&=\frac1{D_\varnothing}
-\frac1{D_{\{Y_1\}}}
-\frac1{D_{\{Y_2\}}}
+\frac1{D_{\boldsymbol{Y}}}
\\
&= y_1y_2\left(\frac1{D_\varnothing D_{\{Y_1\}}D_{\boldsymbol{Y}}}+\frac1{D_\varnothing D_{\{Y_2\}}D_{\boldsymbol{Y}}}\right)
\end{aligned}
```

For $\boldsymbol{Y}=\{y_1,y_2,y_3\}$:
```math
\begin{aligned}
\prod_{i=1}^{3}\Delta_{y_i}\left[\frac{1}{D}\right]
&=
\frac{1}{D_\varnothing}
-\frac{1}{D_{\{Y_1\}}}
-\frac{1}{D_{\{Y_2\}}}
-\frac{1}{D_{\{Y_3\}}}
+\frac{1}{D_{\{Y_1,Y_2\}}}
+\frac{1}{D_{\{Y_1,Y_3\}}}
+\frac{1}{D_{\{Y_2,Y_3\}}}
-\frac{1}{D_{\boldsymbol{Y}}}
\\
&=
y_1y_2y_3\left(
\frac{1}{D_\varnothing D_{\{Y_1\}}D_{\{Y_1,Y_2\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_1\}}D_{\{Y_1,Y_3\}}D_{\boldsymbol{Y}}}
\right.
\\
&\hspace{1.8cm}
+\frac{1}{D_\varnothing D_{\{Y_2\}}D_{\{Y_1,Y_2\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_2\}}D_{\{Y_2,Y_3\}}D_{\boldsymbol{Y}}}
\\
&\hspace{1.8cm}
\left.
+\frac{1}{D_\varnothing D_{\{Y_3\}}D_{\{Y_1,Y_3\}}D_{\boldsymbol{Y}}}
+\frac{1}{D_\varnothing D_{\{Y_3\}}D_{\{Y_2,Y_3\}}D_{\boldsymbol{Y}}}
\right)
\end{aligned}
```

## Notes

- Sublists of `ys` are used as the Lean representation of subsets.
- The ordering of `ys` only matters for producing concrete lists and sums; the final formula is the usual subset expansion.
