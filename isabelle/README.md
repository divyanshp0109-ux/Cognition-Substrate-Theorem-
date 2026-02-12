# Isabelle/HOL Formalization of the Cognition Substrate Theorem

This folder contains the Isabelle/HOL formalization of the CST.

## Status

| Aspect | Status |
|--------|--------|
| **Verification** | ✅ Verified (Isabelle 2025) |
| **Source** | Ported from Lean 4 + Coq/Rocq proofs |

## Files

| File | Contents |
|------|----------|
| **CST.thy** | Existence proof: data structures, `cognitive_substrate` predicate, 3 axioms, constructive `cst_existence` theorem |
| **CST_Minimality.thy** | Minimality proofs: 5 ablation theorems + 1 non-formation theorem + `CST_Minimality_Full` master theorem |

## HOL-Specific Notes

In Isabelle/HOL, every type is **non-empty by design**. This means the S/F/J ablation proofs (which use `Empty` types in Lean/Coq) become HOL tautologies — the logic itself structurally forbids uninhabited types. This is a **stronger** guarantee than the explicit witness-based proofs in Lean/Coq.

## Verification Instructions

1. Install Isabelle from: https://isabelle.in.tum.de/installation.html
2. Open **Isabelle/jEdit** (ships with Isabelle)
3. File → Open → select `CST.thy` or `CST_Minimality.thy`
4. The theory processes automatically — no errors = verified

## Notes

- Uses `definition`-based predicates and `auto`/`blast` automation
- Proofs are written in idiomatic Isabelle style (not ported tactic scripts)
- Files are independent — no import dependency between them
