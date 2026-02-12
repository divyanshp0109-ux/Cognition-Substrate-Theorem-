(*
  Cognition Substrate Theorem (CST) - Isabelle/HOL Formalization
  
  Ported from verified Lean 4 and Coq/Rocq proofs.
  
  This is an ISABELLE-NATIVE proof, using Isabelle's own idioms:
  - auto/simp for automation
  - Isar structured proofs where needed
  - Definition-based predicate (not locale)
  
  Proves:
  1. Trajectory monotonicity (automatic from list indexing)
  2. Cognitive Substrate axioms are satisfiable
  3. CST Existence Theorem (constructive, using unit types)
*)

theory CST
  imports Main
begin

(* ============================================================ *)
(* SECTION 1: Core Data Structures                              *)
(* ============================================================ *)

record 'content epistemic_state =
  es_content :: "'content"
  es_physical_time :: "nat"

type_synonym 'content state_trajectory = "'content epistemic_state list"

definition trajectory_length :: "'content state_trajectory \<Rightarrow> nat" where
  "trajectory_length s = length s"

definition at_step :: "'content state_trajectory \<Rightarrow> nat \<Rightarrow> 'content epistemic_state option" where
  "at_step s n = (if n < length s then Some (s ! n) else None)"

text \<open>Monotonicity: list indexing is gap-free by construction.\<close>
theorem trajectory_is_monotonic:
  assumes "n \<le> m" and "at_step s m \<noteq> None"
  shows "at_step s n \<noteq> None"
  using assms unfolding at_step_def by (auto split: if_split_asm)

(* ============================================================ *)
(* SECTION 2: Operator Type Definitions                         *)
(* ============================================================ *)

record ('content, 'input, 'eval) justification_token =
  jt_prev_content :: "'content option"
  jt_input :: "'input"
  jt_evaluation :: "'eval"
  jt_next_content :: "'content"
  jt_logical_step :: "nat"
  jt_physical_time :: "nat"

record ('content, 'input, 'eval) transition_result =
  tr_new_trajectory :: "'content state_trajectory"
  tr_justification :: "('content, 'input, 'eval) justification_token"
  tr_updated :: "bool"

definition append_to_trajectory :: 
  "'content state_trajectory \<Rightarrow> 'content \<Rightarrow> nat \<Rightarrow> 'content state_trajectory" where
  "append_to_trajectory s c pt = s @ [\<lparr> es_content = c, es_physical_time = pt \<rparr>]"

(* ============================================================ *)
(* SECTION 3: The Cognitive Substrate Predicate                 *)
(* ============================================================ *)

text \<open>
  The Cognitive Substrate: phi must satisfy three axioms.
  - Justified: transitions carry correct evidence
  - Monotonic: existing states are preserved  
  - Advancing: the trajectory grows
\<close>

definition cognitive_substrate ::
  "('input \<Rightarrow> nat \<Rightarrow> 'content state_trajectory \<Rightarrow> 
   ('content, 'input, 'eval) transition_result) \<Rightarrow> bool" where
  "cognitive_substrate phi \<longleftrightarrow>
   (\<forall>i pt s. tr_updated (phi i pt s) \<longrightarrow>
       jt_input (tr_justification (phi i pt s)) = i \<and>
       jt_logical_step (tr_justification (phi i pt s)) = trajectory_length s) \<and>
   (\<forall>i pt s n. at_step s n \<noteq> None \<longrightarrow>
       at_step (tr_new_trajectory (phi i pt s)) n = at_step s n) \<and>
   (\<forall>i pt s. tr_updated (phi i pt s) \<longrightarrow>
       at_step (tr_new_trajectory (phi i pt s)) (trajectory_length s) \<noteq> None)"

(* ============================================================ *)
(* SECTION 4: Minimal Instance (Constructive Existence Proof)   *)
(* ============================================================ *)

type_synonym minimal_content = "unit"
type_synonym minimal_input = "unit"
type_synonym minimal_eval = "unit"

definition get_last_content :: "minimal_content state_trajectory \<Rightarrow> minimal_content option" where
  "get_last_content s = (if s = [] then None else Some (es_content (last s)))"

definition minimal_phi :: 
  "minimal_input \<Rightarrow> nat \<Rightarrow> minimal_content state_trajectory \<Rightarrow>
   (minimal_content, minimal_input, minimal_eval) transition_result" where
  "minimal_phi inp pt s = 
   \<lparr> tr_new_trajectory = append_to_trajectory s () pt,
     tr_justification = \<lparr> jt_prev_content = get_last_content s, jt_input = inp, 
                          jt_evaluation = (), jt_next_content = (),
                          jt_logical_step = trajectory_length s, 
                          jt_physical_time = pt \<rparr>,
     tr_updated = True \<rparr>"

text \<open>The minimal instance satisfies all three axioms.\<close>
lemma minimal_phi_is_substrate: "cognitive_substrate minimal_phi"
  unfolding cognitive_substrate_def minimal_phi_def 
            append_to_trajectory_def at_step_def trajectory_length_def
  by (auto simp: nth_append)

(* ============================================================ *)
(* SECTION 5: The CST Existence Theorem                         *)
(* ============================================================ *)

text \<open>
  CST Existence Theorem: There exists a valid Cognitive Substrate.
  Constructive proof using unit types as witnesses.
\<close>
theorem cst_existence:
  "\<exists>phi :: minimal_input \<Rightarrow> nat \<Rightarrow> minimal_content state_trajectory \<Rightarrow>
          (minimal_content, minimal_input, minimal_eval) transition_result. 
   cognitive_substrate phi"
  using minimal_phi_is_substrate by blast

end
