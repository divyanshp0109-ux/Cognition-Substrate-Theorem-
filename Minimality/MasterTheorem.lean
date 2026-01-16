/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

/-
CST Minimality Master Theorem (v2 - Hybrid Proof Strategy)

Establishes the necessity of all 6 components using two distinct strategies:
1. ABLATION PROOFS (T, S, F, J, ⊕): Removing component leads to contradiction.
2. NON-FORMATION PROOF (Φ): Lack of Protocol leads to uninhabited System Type.

Together with CST_Verified.lean (existence proof), this establishes:
1. EXISTENCE: A valid 6-tuple exists (Constructive)
2. MINIMALITY: No subset works (Ablation)
3. CONSTITUTION: The Protocol constitutes the system (Non-Formation)
-/
import Minimality.Minimality_NoT
import Minimality.Minimality_NoS
import Minimality.Minimality_NoF
import Minimality.Minimality_NoJ
import Minimality.Minimality_NoOplus
import Minimality.Minimality_NoPhi


namespace CST.Minimality

/--
CST MASTER THEOREM

1. Component Necessity: The 5 "Part" ablations rely on constrained counter-models.
2. Protocol Necessity: The "Whole" formulation relies on type dependency.
-/
theorem CST_Minimality_Full :
  -- 1. Structural Ablation Proofs (The Parts are Necessary)
  (∀ C, (∃ (hT : HasTemporalOrdering C), hT.Time = Unit) → False) ∧
  (∀ C [HasTemporalOrdering C], (∃ (hS : HasPersistentIdentity C), hS.State = Empty) → False) ∧
  (∀ C [HasTemporalOrdering C] [HasPersistentIdentity C], (∃ (hF : HasInterpretability C), hF.Evaluation = Empty) → False) ∧
  (∀ C [HasTemporalOrdering C] [HasPersistentIdentity C], (∃ (hJ : HasEpistemicAccountability C), hJ.JustificationToken = Empty) → False) ∧
  (∀ C [HasTemporalOrdering C] (hS : HasPersistentIdentity C), hS.State = Unit → (∀ (hB : @HasBeliefUpdate C _ hS), False)) ∧
  
  -- 2. Protocol Non-Formation Proof (The Whole Requires the Glue)
  (∀ C, (∀ (hT : HasTemporalOrdering C)
           (hS : @HasPersistentIdentity C hT)
           (hF : @HasInterpretability C hT hS)
           (hJ : @HasEpistemicAccountability C hT hS)
           (hB : @HasBeliefUpdate C hT hS),
           IsEmpty (@HasSystematicProtocol C hT hS hF hJ hB))
        → IsEmpty (CognitiveAssembly C)) := by
  
  apply And.intro
  -- 1. NoT
  { exact fun C ⟨hT, h_unit⟩ => Unit_Time_Impossible C hT h_unit }
  apply And.intro
  -- 2. NoS
  { exact fun C _ ⟨hS, h_empty⟩ => Empty_State_Impossible C hS h_empty }
  apply And.intro
  -- 3. NoF
  { exact fun C _ _ ⟨hF, h_empty⟩ => Empty_Eval_Impossible C hF h_empty }
  apply And.intro
  -- 4. NoJ
  { exact fun C _ _ ⟨hJ, h_empty⟩ => Empty_Token_Impossible C hJ h_empty }
  apply And.intro
  -- 5. NoOplus
  { exact fun C _ hS h_unit hB => Unit_State_Impossible C hS h_unit hB }
  
  -- 6. NoPhi (Non-Formation)
  { exact Protocol_NonFormation }

end CST.Minimality
