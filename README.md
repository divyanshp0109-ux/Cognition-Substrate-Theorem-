# The Cognition Substrate Theorem (CST)
## Formal Verification Repository

This repository contains the complete, formally verified proofs for the Cognition Substrate Theorem (CST).

**Verification Tool:** Lean 4 (v4.24.0) with Mathlib
**Automated Prover:** Aristotle
**Status:** ✅ Fully Verified

### 1. Existence Theorem
File: `CST_Verified.lean`
- Formalizes the 6-tuple `⟨S, T, F, ⊕, J, Φ⟩`
- Proves the existence of a valid Cognitive Substrate using constructive Minimal Types (Unit).
- **Status:** Verified

### 2. Minimality Theorems (Necessity)
File: `Minimality/MasterTheorem.lean`
- Proves that **all 6 components** are strictly necessary.
- Uses **two proof strategies**:

| Component | Strategy | Description |
|---|---|---|
| **Temporal (T)** | Ablation | `Time = Unit` → Contradiction |
| **State (S)** | Ablation | `State = Empty` → Contradiction |
| **Inference (F)** | Ablation | `Eval = Empty` → Contradiction |
| **Justification (J)** | Ablation | `Token = Empty` → Contradiction |
| **Belief (⊕)** | Ablation | `State = Unit` → Contradiction (Static system cannot learn) |
| **Protocol (Φ)** | Non-Formation | No Protocol Type → System Construction Impossible |

### Build Instructions

To verify the proofs locally:

```bash
lake exe cache get   # Download pre-compiled Mathlib binaries
lake build           # Compile and check all proofs
```

**Note:** This repository depends on `mathlib4`.
