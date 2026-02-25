/-
Final Coalgebra for the Cognition Substrate Theorem (CST)
FINAL VERSION - Merged from Aristotle Proof Fragments

This file defines the Final H_CST-Coalgebra (νH_CST), representing the 
universal semantic limit of cognitive systems. It proves that every valid 
CST coalgebra has a unique homomorphism into this final system.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: v4.24.0
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

-- ============================================================================
-- SECTION 1: Base Definitions
-- ============================================================================

structure JToken (Content Input Evaluation : Type) where
  prev_content : Option Content
  input : Input
  evaluation : Evaluation
  next_content : Content
  logicalStep : Nat
  physicalTime : Nat
deriving BEq, Repr, DecidableEq

structure TransitionOutput (X Content Input Evaluation : Type) where
  nextState : X
  justification : JToken Content Input Evaluation
  updated : Bool

def H_CST (X Content Input Evaluation : Type) : Type :=
  Input → TransitionOutput X Content Input Evaluation

class CSTCoalgebra (X Content Input Evaluation : Type) where
  len : X → Nat
  obs : X → Nat → Option (Content × Nat)
  F : X → Input → Evaluation
  oplus : X → Content → Nat → X
  alpha : X → H_CST X Content Input Evaluation
  decoration_coherence : ∀ (s : X) (i : Input),
    let res := alpha s i
    res.updated →
    res.justification.input = i ∧
    res.justification.logicalStep = len s ∧
    (len s > 0 →
      res.justification.prev_content = (obs s (len s - 1)).map Prod.fst)
  monotonicity : ∀ (s : X) (i : Input),
    let res := alpha s i
    ∀ step, obs s step ≠ none → obs res.nextState step = obs s step
  productivity : ∀ (s : X) (i : Input),
    let res := alpha s i
    res.updated → obs res.nextState (len s) ≠ none
  len_obs_coherence : ∀ (s : X) (n : Nat), obs s n ≠ none ↔ n < len s

-- ============================================================================
-- SECTION 2: Final Carrier
-- ============================================================================

inductive PathStep (Input Content : Type) where
  | alpha : Input → PathStep Input Content
  | oplus : Content → Nat → PathStep Input Content
deriving BEq, Repr, DecidableEq, Hashable

@[ext]
structure NodeData (Content Input Evaluation : Type) where
  len : Nat
  obs : Nat → Option (Content × Nat)
  F : Input → Evaluation
  alpha_data : Input → (JToken Content Input Evaluation × Bool)

def FinalCarrier (Content Input Evaluation : Type) :=
  List (PathStep Input Content) → NodeData Content Input Evaluation

def Valid (Content Input Evaluation : Type) (f : FinalCarrier Content Input Evaluation) : Prop :=
  ∀ (xs : List (PathStep Input Content)),
    let node := f xs
    (∀ n, node.obs n ≠ none ↔ n < node.len) ∧
    ∀ (i : Input),
      let (jt, b) := node.alpha_data i
      let next_node := f (xs ++ [PathStep.alpha i])
      (b →
        jt.input = i ∧
        jt.logicalStep = node.len ∧
        (node.len > 0 → jt.prev_content = (node.obs (node.len - 1)).map Prod.fst)) ∧
      (∀ step, node.obs step ≠ none → next_node.obs step = node.obs step) ∧
      (b → next_node.obs node.len ≠ none)

def FinalCSTCoalgebraSet (Content Input Evaluation : Type) : Type :=
  { f : FinalCarrier Content Input Evaluation // Valid Content Input Evaluation f }

-- ============================================================================
-- SECTION 3: Final Coalgebra Instance
-- ============================================================================

instance (Content Input Evaluation : Type) : CSTCoalgebra (FinalCSTCoalgebraSet Content Input Evaluation) Content Input Evaluation where
  len f := (f.val []).len
  obs f := (f.val []).obs
  F f := (f.val []).F
  oplus f c n := ⟨fun xs => f.val (PathStep.oplus c n :: xs), by
    intro xs
    apply (f.property (PathStep.oplus c n :: xs))⟩
  alpha f i :=
    let node := f.val []
    let (jt, b) := node.alpha_data i
    { nextState := ⟨fun xs => f.val (PathStep.alpha i :: xs), by
        intro xs
        apply (f.property (PathStep.alpha i :: xs))⟩,
      justification := jt,
      updated := b }
  decoration_coherence f i := by
    let node := f.val []
    let (jt, b) := node.alpha_data i
    have h := (f.property []).2 i
    simp only [] at h
    exact h.1
  monotonicity f i step h_obs := by
    let node := f.val []
    have h := (f.property []).2 i
    simp only [] at h
    exact h.2.1 step h_obs
  productivity f i h_upd := by
    let node := f.val []
    have h := (f.property []).2 i
    simp only [] at h
    exact h.2.2 h_upd
  len_obs_coherence f n := by
    exact (f.property []).1 n

-- ============================================================================
-- SECTION 4: Terminal Map
-- ============================================================================

def follow_path {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation]
    (s : X) : List (PathStep Input Content) -> X
  | [] => s
  | PathStep.alpha i :: rest =>
      follow_path (X := X) (Content := Content) (Input := Input) (Evaluation := Evaluation)
        (inst := inst) (inst.alpha s i).nextState rest
  | PathStep.oplus c n :: rest =>
      follow_path (X := X) (Content := Content) (Input := Input) (Evaluation := Evaluation)
        (inst := inst) (inst.oplus s c n) rest

lemma follow_path_append {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation]
    (s : X) (xs ys : List (PathStep Input Content)) :
    follow_path (inst := inst) s (xs ++ ys) =
      follow_path (inst := inst) (follow_path (inst := inst) s xs) ys := by
  induction xs generalizing s with
  | nil =>
      simp [follow_path]
  | cons step rest ih =>
      cases step with
      | alpha i =>
          simp [follow_path, ih]
      | oplus c n =>
          simp [follow_path, ih]

def terminal_map_val {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation]
    (s : X) : FinalCarrier Content Input Evaluation :=
  fun xs =>
    let s' := follow_path (inst := inst) s xs
    { len := inst.len s'
      obs := inst.obs s'
      F := inst.F s'
      alpha_data := fun i =>
        let res := inst.alpha s' i
        (res.justification, res.updated) }

theorem terminal_map_valid {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation]
    (s : X) : Valid Content Input Evaluation (terminal_map_val (inst := inst) s) := by
  intro xs
  let s' := follow_path (inst := inst) s xs
  constructor
  · intro n
    simpa [terminal_map_val, s'] using (inst.len_obs_coherence s' n)
  · intro i
    let res := inst.alpha s' i
    have h_append :
        follow_path (inst := inst) s (xs ++ [PathStep.alpha i]) = res.nextState := by
      simpa [s', res, follow_path] using
        (follow_path_append (inst := inst) s xs [PathStep.alpha i])
    constructor
    · intro h_upd
      simpa [terminal_map_val, s', res] using (inst.decoration_coherence s' i h_upd)
    constructor
    · intro step h_step
      have h_mono := inst.monotonicity s' i step h_step
      simpa [terminal_map_val, s', res, h_append] using h_mono
    · intro h_upd
      have h_prod := inst.productivity s' i h_upd
      simpa [terminal_map_val, s', res, h_append] using h_prod

def terminal_map {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation]
    (s : X) : FinalCSTCoalgebraSet Content Input Evaluation :=
  ⟨terminal_map_val s, terminal_map_valid s⟩

-- ============================================================================
-- SECTION 5: Universality
-- ============================================================================

structure CSTCoalgebraHomomorphism
    (X Y Content Input Evaluation : Type)
    [src : CSTCoalgebra X Content Input Evaluation]
    [tgt : CSTCoalgebra Y Content Input Evaluation] where
  toFun : X → Y
  map_len : ∀ s, tgt.len (toFun s) = src.len s
  map_obs : ∀ s n, tgt.obs (toFun s) n = src.obs s n
  map_F : ∀ s i, tgt.F (toFun s) i = src.F s i
  map_oplus : ∀ s c n, toFun (src.oplus s c n) = tgt.oplus (toFun s) c n
  map_alpha_updated : ∀ s i, (tgt.alpha (toFun s) i).updated = (src.alpha s i).updated
  map_alpha_justification : ∀ s i, (tgt.alpha (toFun s) i).justification = (src.alpha s i).justification
  map_alpha_nextState : ∀ s i, (tgt.alpha (toFun s) i).nextState = toFun (src.alpha s i).nextState

def final_homomorphism {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation] :
    CSTCoalgebraHomomorphism X (FinalCSTCoalgebraSet Content Input Evaluation) Content Input Evaluation where
  toFun := terminal_map
  map_len s := by
    change (terminal_map_val (inst := inst) s []).len = inst.len s
    simp [terminal_map_val, follow_path]
  map_obs s n := by
    change (terminal_map_val (inst := inst) s []).obs n = inst.obs s n
    simp [terminal_map_val, follow_path]
  map_F s i := by
    change (terminal_map_val (inst := inst) s []).F i = inst.F s i
    simp [terminal_map_val, follow_path]
  map_oplus s c n := by
    apply Subtype.eq
    funext xs
    change terminal_map_val (inst := inst) (inst.oplus s c n) xs =
      terminal_map_val (inst := inst) s (PathStep.oplus c n :: xs)
    simp [terminal_map_val, follow_path]
  map_alpha_updated s i := by
    change ((terminal_map_val (inst := inst) s []).alpha_data i).2 = (inst.alpha s i).updated
    simp [terminal_map_val, follow_path]
  map_alpha_justification s i := by
    change ((terminal_map_val (inst := inst) s []).alpha_data i).1 = (inst.alpha s i).justification
    simp [terminal_map_val, follow_path]
  map_alpha_nextState s i := by
    apply Subtype.eq
    funext xs
    change terminal_map_val (inst := inst) s (PathStep.alpha i :: xs) =
      terminal_map_val (inst := inst) (inst.alpha s i).nextState xs
    simp [terminal_map_val, follow_path]

lemma hom_ext {X Y Content Input Evaluation : Type}
    [src : CSTCoalgebra X Content Input Evaluation]
    [tgt : CSTCoalgebra Y Content Input Evaluation]
    (f g : CSTCoalgebraHomomorphism X Y Content Input Evaluation)
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

lemma hom_to_terminal_val_eq {X Content Input Evaluation : Type}
    [inst : CSTCoalgebra X Content Input Evaluation]
    (h : CSTCoalgebraHomomorphism X (FinalCSTCoalgebraSet Content Input Evaluation) Content Input Evaluation)
    (s : X) (xs : List (PathStep Input Content)) :
    (h.toFun s).val xs = terminal_map_val s xs := by
  induction xs generalizing s with
  | nil =>
      apply NodeData.ext
      · simpa [terminal_map_val, follow_path] using h.map_len s
      · funext n
        simpa [terminal_map_val, follow_path] using h.map_obs s n
      · funext i
        simpa [terminal_map_val, follow_path] using h.map_F s i
      · funext i
        apply Prod.ext
        · simpa [terminal_map_val, follow_path] using h.map_alpha_justification s i
        · simpa [terminal_map_val, follow_path] using h.map_alpha_updated s i
  | cons step rest ih =>
      cases step with
      | alpha i =>
          have h_alpha : (h.toFun s).val (PathStep.alpha i :: rest) =
              (h.toFun (inst.alpha s i).nextState).val rest := by
            simpa [CSTCoalgebra.alpha] using
              (congrArg (fun z => (Subtype.val z) rest) (h.map_alpha_nextState s i))
          calc
            (h.toFun s).val (PathStep.alpha i :: rest)
                = (h.toFun (inst.alpha s i).nextState).val rest := h_alpha
            _ = terminal_map_val (inst.alpha s i).nextState rest := ih (inst.alpha s i).nextState
            _ = terminal_map_val s (PathStep.alpha i :: rest) := by
                  simp [terminal_map_val, follow_path]
      | oplus c n =>
          have h_oplus : (h.toFun (inst.oplus s c n)).val rest =
              (h.toFun s).val (PathStep.oplus c n :: rest) := by
            simpa [CSTCoalgebra.oplus] using
              (congrArg (fun z => (Subtype.val z) rest) (h.map_oplus s c n))
          calc
            (h.toFun s).val (PathStep.oplus c n :: rest)
                = (h.toFun (inst.oplus s c n)).val rest := h_oplus.symm
            _ = terminal_map_val (inst.oplus s c n) rest := ih (inst.oplus s c n)
            _ = terminal_map_val s (PathStep.oplus c n :: rest) := by
                  simp [terminal_map_val, follow_path]

theorem final_coalgebra_universality {X Content Input Evaluation : Type} [inst : CSTCoalgebra X Content Input Evaluation] :
    ∃! (h : CSTCoalgebraHomomorphism X (FinalCSTCoalgebraSet Content Input Evaluation) Content Input Evaluation), True := by
  use final_homomorphism
  simp only [true_and]
  intro h _
  apply hom_ext
  funext s
  apply Subtype.eq
  funext xs
  rw [hom_to_terminal_val_eq h s xs]
  rfl
