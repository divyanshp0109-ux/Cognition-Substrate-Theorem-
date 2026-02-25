# Lean 4 Coalgebraic Formalization of the Cognition Substrate Theorem

This folder contains the **coalgebraic re-encoding** of the CST in Lean 4,
formalizing the theorem within the theory of **H_CST-coalgebras** — a
category-theoretic framework that captures the structural dynamics of any valid
cognitive substrate.

> **Status: Work in Progress.**
> The base formalization is complete and verified. All core theorems below
> compile with zero errors in Lean 4 v4.24.0 + Mathlib v4.24.0, with no
> `sorry` placeholders. Extended results (e.g. a full categorical development)
> are ongoing.

This formalization is **supplementary** to the original type-theoretic
verification in `CST_Verified.lean` and `Minimality/` at the repository root.
Both verify the same theorem — this coalgebraic encoding provides an
independent, semantically richer perspective.

---

## Files

| File | Contents | Status |
|------|----------|--------|
| **`CST_Coalgebraic.lean`** | Defines the `H_CST` endofunctor and `CSTCoalgebra` typeclass with 3 axioms. Constructs a minimal existence witness, proves cognitive bisimulation, ablation results, and the Minimality Master Theorem. | ✅ Verified |
| **`CST_Coalgebraic_Universality.lean`** | Abstract version with opaque carrier `X`. Proves `CST_Coalgebraic_Universality`: the six structural requirements (Temporal Ordering, Persistence, Interpretability, Accountability, Plasticity, Protocol) are universal consequences of the axioms for *any* CST coalgebra. | ✅ Verified |
| **`FinalCoalgebra.lean`** | Defines `FinalCSTCoalgebraSet` (the terminal object νH_CST) as path-indexed `NodeData` trees. Constructs the terminal map and proves `final_coalgebra_universality`: every CST coalgebra has a **unique** homomorphism into the final system. | ✅ Verified |

---

## The Endofunctor

The CST 6-tuple `C = ⟨T, S, F, J, ⊕, Φ⟩` is encoded as a coalgebra for:

```
H_CST(X) = Input → (X × JToken × Bool)
```

The structure map `α : X → H_CST(X)` is the transition operator Φ.
The three coalgebra axioms are:
1. **Decoration Coherence** — every transition is self-documenting (Axiom J)
2. **Monotonicity** — past observations are preserved (Axioms T, S, ⊕)
3. **Productivity** — a successful transition always extends the record (Axiom Φ)

---

## Principal Theorems

| Theorem | Statement |
|---------|-----------|
| `cst_coalgebra_existence` | `Coalg(H_CST)` is non-empty |
| `CST_Coalgebraic_Universality` | All 6 structural requirements hold for *any* H_CST-coalgebra |
| `final_coalgebra_universality` | The terminal coalgebra νH_CST exists; every CST coalgebra maps into it uniquely |

---

## Build Instructions

From the **repository root** (Lean 4 v4.24.0 + Mathlib v4.24.0 required):

```bash
# Download pre-compiled Mathlib cache (saves significant build time)
lake exe cache get

# Verify each file individually
lake env lean "coalgebraic formalisation initial formalisation results/CST_Coalgebraic.lean"
lake env lean "coalgebraic formalisation initial formalisation results/CST_Coalgebraic_Universality.lean"
lake env lean "coalgebraic formalisation initial formalisation results/FinalCoalgebra.lean"
```

All three should complete with no errors.

---

## Design Notes

- Uses a **concrete `Trajectory`** (List-based state) as the core carrier for
  tractable proofs, rather than relying on Mathlib's abstract coalgebra API.
- The final coalgebra is encoded via `List PathStep → NodeData` (a
  coinductive-style function space) to avoid Lean's productivity checker
  constraints on genuine coinductive types.
- Proof assistance provided by [Aristotle](https://aristotle.harmonic.fun);
  all outputs independently verified.

---

## Relation to the Paper

> Pandya, D. (2026). *The Cognition Substrate Theorem*.
> Submitted to the *Journal of Logic and Computation*.
