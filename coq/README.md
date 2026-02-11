# Coq/Rocq Formalization of the Cognition Substrate Theorem

This folder contains the Coq/Rocq port of the CST, originally verified in Lean 4.

## Status

| Aspect | Status |
|--------|--------|
| **Verification** | ✅ Verified (Rocq Prover 9.0.1) |
| **Source** | Ported from Lean 4 + Aristotle AI proofs |

## Files

| File | Contents |
|------|----------|
| **CST.v** | Existence proof: 6-tuple structure, 3 axioms, constructive `cst_existence` theorem |
| **CST_Minimality.v** | Minimality proofs: 5 ablation theorems + 1 non-formation theorem + `CST_Minimality_Full` master theorem |

## Verification Instructions

### 1. Install Rocq Platform

Download from: https://github.com/coq/platform/releases

For Windows: Download the Rocq Platform 9.0 `.exe` installer (~2.2 GB).

### 2. Verify the Proofs

```powershell
# Set environment (adjust path if needed)
$env:PATH = "C:\Rocq-Platform~9.0~2025.08\bin;" + $env:PATH
$env:ROCQLIB = "C:\Rocq-Platform~9.0~2025.08\lib\coq"

# Compile both files (independent, any order)
coqc CST.v
coqc CST_Minimality.v
```

Clean compilation with no errors = ✅ verified.

## Notes

- Uses `Record` and `Class` mechanisms to encode the CST type classes
- Proofs use standard tactics (`simpl`, `rewrite`, `lia`, `discriminate`, `destruct`)
- Both proofs are constructive: existence via `unit` types, impossibility via `EmptyType`
- Files are independent — no import dependency between them
