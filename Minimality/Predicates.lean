/-
CST Minimality Proofs - Predicate Definitions (v2)

These are the 6 structural "checkboxes" that any cognitive system must satisfy.
Each predicate is intentionally WEAK -- just enough to enable independence proofs.

Aligned with CST_Verified.lean (logical time separation model).
Prepared for Aristotle theorem prover.
-/
namespace CST.Minimality

/-! ## Predicate 1: Temporal Ordering (T)
Time must have discrete progression with a successor function. -/
class HasTemporalOrdering (C : Type) where
  Time : Type
  next : Time → Time
  progress : ∀ t, next t ≠ t

/-! ## Predicate 2: Persistent Identity / State Space (S)
States must exist and the system must have memory (history). -/
class HasPersistentIdentity (C : Type) [HasTemporalOrdering C] where
  State : Type
  stateInhabited : Nonempty State  -- At least one state must exist

/-! ## Predicate 3: Interpretability / Inference Operator (F)
The system must be able to evaluate inputs against states. -/
class HasInterpretability (C : Type) [HasTemporalOrdering C] [HasPersistentIdentity C] where
  Input : Type
  Evaluation : Type
  evalInhabited : Nonempty Evaluation  -- Must produce actual evaluations
  infer : HasPersistentIdentity.State C → Input → Evaluation

/-! ## Predicate 4: Epistemic Accountability / Justification Operator (J)
Every state transition must produce a justification token.
The key constraint: distinct states MUST produce justifications (non-trivial). -/
class HasEpistemicAccountability (C : Type) [HasTemporalOrdering C] [HasPersistentIdentity C] where
  JustificationToken : Type
  tokenInhabited : Nonempty JustificationToken  -- Tokens must exist
  justify : HasTemporalOrdering.Time C →
            HasPersistentIdentity.State C →
            HasPersistentIdentity.State C →
            Option JustificationToken
  -- Nontriviality: If states are distinct, justification MUST be produced
  nontrivial : ∀ (t : HasTemporalOrdering.Time C)
               (s s' : HasPersistentIdentity.State C),
               s ≠ s' → justify t s s' ≠ none

/-! ## Predicate 5: Belief Update / Revision Operator (⊕)
The system must be able to revise beliefs.
The key constraint: revision must actually change something (non-identity). -/
class HasBeliefUpdate (C : Type) [HasTemporalOrdering C] [HasPersistentIdentity C] where
  revise : HasPersistentIdentity.State C →
           HasPersistentIdentity.State C →
           HasPersistentIdentity.State C
  -- Non-identity: There exist states where revision produces something new
  non_identity : ∃ (s1 s2 : HasPersistentIdentity.State C), revise s1 s2 ≠ s1

/-! ## Predicate 6: Systematic Protocol / Transition Operator (Φ)
The system must have a coordinated transition function that produces new states. -/
class HasSystematicProtocol (C : Type)
    [HasTemporalOrdering C] [HasPersistentIdentity C]
    [HasInterpretability C] [HasEpistemicAccountability C]
    [HasBeliefUpdate C] where
  transition : HasTemporalOrdering.Time C →
               HasInterpretability.Input C →
               HasPersistentIdentity.State C →
               HasPersistentIdentity.State C
  -- Advancement: Transition always produces a state
  advances : ∀ (t : HasTemporalOrdering.Time C)
             (i : HasInterpretability.Input C)
             (s : HasPersistentIdentity.State C),
             ∃ s', transition t i s = s'

end CST.Minimality
