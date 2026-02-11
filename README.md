# The Cognition Substrate Theorem (CST)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18436371.svg)](https://doi.org/10.5281/zenodo.18436371)

## Formal Verification Repository

This repository contains the complete, formally verified proofs for the Cognition Substrate Theorem (CST).

**Verification Tools:** Lean 4 (v4.24.0) with Mathlib, Coq/Rocq 9.0.1  
**Automated Prover:** Aristotle  
**Status:** ✅ Fully Verified (Lean 4 + Coq)

---

## Citation

If you use this formalization in your research, please cite:

> Pandya, D. (2026). The Cognition Substrate Theorem (CST) (Version v1). Zenodo. https://doi.org/10.5281/zenodo.18436371

**BibTeX:**
```bibtex
@software{pandya2026cst,
  author       = {Pandya, Divyansh},
  title        = {The Cognition Substrate Theorem (CST)},
  year         = 2026,
  publisher    = {Zenodo},
  version      = {v1},
  doi          = {10.5281/zenodo.18436371},
  url          = {https://doi.org/10.5281/zenodo.18436371}
}
```

---

## Verified In

| Language | Existence Proof | Minimality Proofs | Status |
|----------|----------------|-------------------|--------|
| **Lean 4** (v4.24.0 + Mathlib) | `CST_Verified.lean` | `Minimality/MasterTheorem.lean` | ✅ Verified |
| **Coq/Rocq** (9.0.1) | `coq/CST.v` | `coq/CST_Minimality.v` | ✅ Verified |

---

## What Is Proved

### 1. Existence Theorem
Formalizes the 6-tuple `⟨S, T, F, ⊕, J, Φ⟩` and proves the existence of a valid Cognitive Substrate using constructive Minimal Types (Unit).

### 2. Minimality Theorems (Necessity)
Proves that **all 6 components** are strictly necessary, using **two proof strategies**:

| Component | Strategy | Description |
|---|---|---|
| **Temporal (T)** | Ablation | `Time = Unit` → Contradiction |
| **State (S)** | Ablation | `State = Empty` → Contradiction |
| **Inference (F)** | Ablation | `Eval = Empty` → Contradiction |
| **Justification (J)** | Ablation | `Token = Empty` → Contradiction |
| **Belief (⊕)** | Ablation | `State = Unit` → Contradiction (Static system cannot learn) |
| **Protocol (Φ)** | Non-Formation | No Protocol Type → System Construction Impossible |

Both the Lean 4 and Coq formalizations prove the same theorems independently.

---

## Build Instructions (Lean 4)

To verify the proofs locally:

```bash
lake exe cache get   # Download pre-compiled Mathlib binaries
lake build           # Compile and check all proofs
```

**Note:** This repository depends on `mathlib4`.

---

## License

MIT License - See [LICENSE](LICENSE) for details.
