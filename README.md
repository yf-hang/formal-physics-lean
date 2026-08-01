# CosmoLattice (TwoSiteBooleanLattice)

This project formalizes two equivalent descriptions of the finite-difference expansion used for studying Boolean-lattice formalization of two-site $\ell$-loop cosmological wavefunction.

The relevant paper: "A Boolean-Lattice Perspective for All-Loop Two-Site Cosmological Wavefunction" [arXiv:2605.30797](https://arxiv.org/abs/2605.30797) (v2 is in preparation and will add more mathematical analysis).

## A. Finite-Difference Identity

The file `FiniteDiff.lean` formalizes an alternating subset expansion for iterated finite differences. The main identity expresses an iterated finite difference as an alternating sum over all subsets of the shifts:

$$
\prod_{a\in\mathbf{Y}} \Delta_{a}\; f(D) = \sum_{V \subseteq \mathbf{Y}} (-1)^{|V|}\; f\bigg(D + \sum_{a \in V} a\bigg)
$$

where $\mathbf{Y}=\{Y_1,\ldots,Y_{\ell+1}\}$ is the set of internal energies carried on propagators and $\Delta$ represents the finite difference operator defined by

$$
\Delta_h f(D) = f(D) - f(D + h)
$$

In the Lean development, the finite set $\mathbf{Y}$ is represented by an ordered list `ys`, and its subsets $V$ are represented by `ys.sublists`. The order inherited from the list is only used to compute the finite sum of shifts.

### Main Definitions

#### 1). One-step finite difference

```lean
def finiteDiff {A K : Type*} [Add A] [Sub K]
    (h : A) (f : A → K) : A → K :=
  fun D => f D - f (D + h)
```

This defines the finite-difference operator

$$
\Delta_h f(D)=f(D)-f(D+h)
$$

#### 2). Iterated finite difference

```lean
def iteratedFiniteDiff {A K : Type*} [Add A] [Sub K]
    (ys : List A) (f : A → K) : A → K :=
  ys.foldr (fun h g => finiteDiff h g) f
```

For example, if

```lean
ys = [y₁, y₂, y₃]
```

then

$$
\mathrm{iteratedFiniteDiff}\; ys\; f =\Delta_{y_1}\bigl(\Delta_{y_2}(\Delta_{y_3}f)\bigr)
$$

#### 3). Alternating sublist expansion

```lean
def finiteDiffExpansion {A K : Type*}
    [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) : K :=
  (ys.sublists.map fun V =>
    (-1 : K) ^ V.length * f (D + V.sum)).sum
```

This represents

$$
\sum_{V\subseteq ys.\mathrm{sublists}} (-1)^{|V|} f\left(D+\sum_{a\in V}a\right)
$$

### Main Theorem

The central theorem states that the iterated finite difference agrees with the alternating sublist expansion:

```lean
theorem iteratedFiniteDiff_eq_sum_subsets
    {A K : Type*} [AddCommMonoid A] [CommRing K]
    (ys : List A) (f : A → K) (D : A) :
    iteratedFiniteDiff ys f D =
      finiteDiffExpansion ys f D
```

### Proof Idea

The proof proceeds by induction on the list `ys`. 

For the empty list, `ys = []`, no finite-difference operator is applied, so

$$
\mathrm{iteratedFiniteDiff}\;[\;]\;f\;D=f(D)
$$

The only sublist of the empty list is the empty list itself. Therefore,

$$
\mathrm{finiteDiffExpansion}\;[\;]\;f\;D=(-1)^0f(D+0)=f(D)
$$

Lean proves this case by simplifying the definitions:

```lean
simp [iteratedFiniteDiff, finiteDiffExpansion]
```

#### Inductive step

Assume the list has the form `h :: ys`, and assume the identity has already been proved for the shorter list `ys`. The induction is performed with

```lean
induction ys generalizing D
```

so the induction hypothesis is available at any argument $D$. In particular, it can be used both at $D$ and at $D+h$.

Expanding the first finite-difference operator gives

```lean
iteratedFiniteDiff ys f D - iteratedFiniteDiff ys f (D + h) = finiteDiffExpansion (h :: ys) f D
```lean

The induction hypothesis is then applied to both terms:

```lean
rw [ih D, ih (D + h)]
```

This reduces the goal to

```lean
finiteDiffExpansion ys f D - finiteDiffExpansion ys f (D + h) = finiteDiffExpansion (h :: ys) f D
```

It remains to compare the sublists of `h :: ys` with those of `ys`.

Every sublist of `h :: ys` is obtained uniquely in one of two ways:

1. `h` is not selected, giving a sublist `V` of `ys`;
2. `h` is selected, giving a sublist of the form `h :: V`.

Lean expresses this decomposition through `List.sublists_cons`, which rewrites the sublists of `h :: ys` as

```lean
ys.sublists.flatMap (fun V => [V, h :: V])
```

For each `V ∈ ys.sublists`, the sublist `V` contributes

$$
(-1)^{|V|}
f\left(D+\sum_{a\in V}a\right)
$$

The sublist `h :: V` contributes

$$
\begin{aligned}
(-1)^{|h::V|}
f\left(D+\sum_{a\in h::V}a\right) 
&=(-1)^{|V|+1}f\left(D+h+\sum_{a\in V}a\right) 
\\
&= -(-1)^{|V|}f\left(D+h+\sum_{a\in V}a\right)
\end{aligned}
$$

Therefore, the expansion over all sublists of `h :: ys` becomes

$$
\sum_{V\subseteq ys.\mathrm{sublists}}
(-1)^{|V|}
f\left(D+\sum_{a\in V}a\right)\; - \;\sum_{V\subseteq ys.\mathrm{sublists}}
(-1)^{|V|} f\left(D+h+\sum_{a\in V}a\right)
$$

which is exactly the expression obtained after applying the induction hypothesis.

The auxiliary lemma `list_sum_flatMap_pair` separates the two contributions associated with `V` and `h :: V`. The lemma `list_sum_map_neg` moves the extra minus sign from each term to the outside of the corresponding list sum. After these rewrites, the remaining equality is a straightforward ring identity.


### Specialization to $\frac{1}{D}$

The file then specializes the general identity to the function:

$$
f(D) = \frac{1}{D}
$$

The shifted denominator is defined as

```lean
def shiftedD {K : Type*} [Add K] [Zero K] (D : K) (V : List K) : K :=
  D + V.sum
```

This represents

$$
D_V = D + \sum_{a \in V} a
$$

The final theorem is

```lean
theorem finiteDiff_inv_eq_sum_subsets
    {K : Type*} [Field K] (ys : List K) (D : K) :
    iteratedFiniteDiff ys (fun x : K => 1 / x) D =
      (ys.sublists.map fun V => (-1 : K) ^ V.length / shiftedD D V).sum
```

Mathematically, this is

$$
\prod_i \Delta_{a_i} \left(\frac{1}{D}\right) = \sum_{V \subseteq \mathbf{Y}} \frac{(-1)^{|V|}}{D_V}
$$

## Local AI proof completion with Ollama

`AI_Proof_Demo` provides a small generate-and-check loop for Lean proofs. It sends the
proof template and relevant project source to a model already installed in local Ollama,
extracts the proposed tactics, and runs Lean on every candidate. A candidate containing
`sorry`, `admit`, or `axiom` is rejected before Lean is invoked. If Lean reports an error,
the diagnostics are sent back to the model for the next attempt.

The default model is `gpt-oss:20b`. Start Ollama and run:

```bash
ollama serve
python3 AI_Proof_Demo/ollama_prove.py
```

Choose another installed model or change the retry count with:

```bash
python3 AI_Proof_Demo/ollama_prove.py \
  --model phi4-mini:latest \
  --attempts 5
```

The model can also be selected through `OLLAMA_MODEL`. `OLLAMA_URL` changes the server
address when Ollama is not listening on `http://127.0.0.1:11434`.

For `gpt-oss:20b`, the script defaults to prompt-only JSON output and then parses the
returned text. This avoids an Ollama schema-mode behavior where the model can report
`done=true` with an empty `response`. If you use a model that handles Ollama's structured
output reliably, enable it explicitly:

```bash
python3 AI_Proof_Demo/ollama_prove.py --json-schema
```

Only a Lean-verified candidate is written to
`AI_Proof_Demo/completion.txt` and `CosmoLattice/AIProofGenerated.lean`. Failed attempts
leave those files unchanged. To skip generation and recheck the saved completion, run:

```bash
python3 AI_Proof_Demo/ollama_prove.py --verify-only
# The original entry point remains available as an alias:
python3 AI_Proof_Demo/assemble_and_verify.py
```

To use the loop for another theorem, put exactly one line containing
`-- AI_PROOF_HOLE` inside an existing `by` proof in a template, then pass that template,
its relevant Lean source files, and the desired output paths:

```bash
python3 AI_Proof_Demo/ollama_prove.py \
  --template path/to/PartialProof.lean.template \
  --context CosmoLattice/FiniteDiff.lean \
  --context CosmoLattice/AnotherDependency.lean \
  --completion path/to/completion.txt \
  --output CosmoLattice/AIProofGenerated.lean
```

Run the Python checks with:

```bash
python3 -m unittest discover -s AI_Proof_Demo -p 'test_*.py' -v
```

## B. Maximal-Chain Expansion

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
\prod_{r=0}^{M}\frac{1}{D+\sigma_r} - \prod_{r=0}^{M}\frac{1}{D+h+\sigma_r} = h\sum_{j=0}^{M} \left(\prod_{r=0}^{j}\frac{1}{D+\sigma_r}\right) \left(\prod_{r=j}^{M}\frac{1}{D+h+\sigma_r} \right)
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
