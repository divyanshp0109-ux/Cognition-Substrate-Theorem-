/-
A CognitiveSystem is any type that satisfies ALL 6 predicates.
This is the "Gold Standard" benchmark for minimality proofs.

Aligned with CST_Verified.lean.
-/
import Minimality.Predicates

namespace CST.Minimality

/-- 
Utility: IsEmpty type class (avoids strict dependency on full Mathlib).
We define it here to make the Proofs self-contained.
-/
class IsEmpty (α : Sort u) : Prop where
  false : α → False

/-- A full CognitiveSystem has all 6 components. -/
class CognitiveSystem (C : Type) extends
    HasTemporalOrdering C,
    HasPersistentIdentity C,
    HasInterpretability C,
    HasEpistemicAccountability C,
    HasBeliefUpdate C,
    HasSystematicProtocol C

/-- 
IsCognitiveSystem: A type C is a CognitiveSystem iff all 6 instances exist.
This is what the counter-models will fail to satisfy.
-/
def IsCognitiveSystem (C : Type) : Prop :=
  ∃ (hT : HasTemporalOrdering C)
    (hS : @HasPersistentIdentity C hT)
    (hF : @HasInterpretability C hT hS)
    (hJ : @HasEpistemicAccountability C hT hS)
    (hB : @HasBeliefUpdate C hT hS)
    (hP : @HasSystematicProtocol C hT hS hF hJ hB), True

end CST.Minimality
