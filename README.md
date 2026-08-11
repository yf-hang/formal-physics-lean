# Formal Physics Lean Projects

## 1. CosmoLattice

This project formalizes in Lean the finite-difference identity underlying the Boolean-lattice description of the two-site $\ell$-loop cosmological wavefunction. It proves that iterated finite differences of $1/D$ are equal to an alternating sum over subsets of the internal-energy shifts.

Relevant paper: [arXiv:2605.30797](https://arxiv.org/pdf/2605.30797).

Proof note: [Finite-Difference Identity](CosmoLattice/documents/FiniteDiffProof.pdf).

### Local LLM Proof Completion

Building on this formalization, `AI_Proof_Demo` provides a local generate-and-verify
workflow using `deepseek-ai/DeepSeek-Prover-V2-7B`. The model generates a candidate tactic
for the single `-- AI_PROOF_HOLE`, and Lean checks the assembled theorem. Candidates that
contain `sorry`, `admit`, or `axiom` are rejected; when verification fails, Lean's
diagnostics are passed back to the model for the next attempt. Output is saved only after
Lean accepts the proof.

### Setup

From the repository root, create a virtual environment and install the dependencies:

```bash
python3 -m venv --system-site-packages .venv-deepseek
.venv-deepseek/bin/python -m pip install \
  'transformers==4.51.3' 'accelerate==1.6.0' \
  'sentencepiece==0.2.0' 'safetensors>=0.4.3'
```

Before the first run, review `AI_Proof_Demo/config.json`. Set `"offline": false` to download
the configured model, then switch it back to `true` once the model is cached for fully
local execution.

### Generate and verify

Run the proof-completion loop with:

```bash
.venv-deepseek/bin/python AI_Proof_Demo/ai_prove.py
```

The script reads its default settings from `AI_Proof_Demo/config.json`. After Lean accepts
a candidate, it saves the tactic to `AI_Proof_Demo/completion.txt` and the assembled theorem
to `AI_Proof_Demo/AIProofGenerated.lean`. Use `--config path/to/config.json` to select another
configuration, or pass an option such as `--attempts 1` to override an individual setting.

To check a saved completion without loading the model, set `"verify_only": true` and run
the same command. Alternatively, use the standalone verification entry point:

```bash
.venv-deepseek/bin/python AI_Proof_Demo/assemble_and_verify.py
```

The generated target imports `CosmoLattice.FiniteDiff`, which provides the definitions and
algebraic helper lemmas used by the proof.

## 2. KKEquivTheorem

This project formalizes the gravitational equivalence theorem for Kaluza–Klein gravity in Lean. GRET relates the scattering amplitudes of massive KK gravitons to those of their corresponding gravitational Goldstone bosons, providing a simpler description of high-energy KK graviton scattering and its underlying gauge/gravity structure.

Relevant paper: [arXiv:2406.12713](https://arxiv.org/pdf/2406.12713).
