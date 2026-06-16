/-
Copyright (c) 2026 Sayan Kumar Chaki, Antoine Gourru, Julien Velcin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayan Kumar Chaki, Antoine Gourru, Julien Velcin
-/
import Mathlib

/-!
# Core Definitions for Emergent Fairness
-/

namespace FairnessEmergence

-- ============================================
-- SECTION 1: ALLOCATION SPACE
-- ============================================

def RawAllocation (N K : ℕ) := Fin N → Fin K → ℝ
def Capacity (K : ℕ) := Fin K → ℝ

structure Allocation (N K : ℕ) (C : Capacity K) where
  val : RawAllocation N K
  nonneg : ∀ i k, val i k ≥ 0
  cap : ∀ k, ∑ i, val i k ≤ C k

instance (N K : ℕ) (C : Capacity K) :
    TopologicalSpace (Allocation N K C) :=
  TopologicalSpace.induced (fun x => x.val) Pi.topologicalSpace

-- ============================================
-- SECTION 2: CNSS
-- ============================================

noncomputable def CNSS
    (N K : ℕ) (C : Capacity K)
    (x : Allocation N K C)
    (i : Fin N) : ℝ :=
  ∑ k, x.val i k

lemma cnss_nonneg
    (N K : ℕ) (C : Capacity K)
    (x : Allocation N K C)
    (i : Fin N) : CNSS N K C x i ≥ 0 := by
  unfold CNSS
  apply Finset.sum_nonneg
  intro k _
  exact x.nonneg i k

-- ============================================
-- SECTION 3: WEIGHTS
-- ============================================

def SurvivalProb (N : ℕ) := Fin N → ℝ
def PrioritarianWeights (N : ℕ) := Fin N → ℝ
def CareWeights (N : ℕ) := Fin N → ℝ

-- ============================================
-- SECTION 4: SIX FAIRNESS METRICS
-- ============================================

noncomputable def ESG
    (N K : ℕ) (C : Capacity K)
    (p : SurvivalProb N)
    (x : Allocation N K C) : ℝ :=
  ∑ i, p i * CNSS N K C x i

noncomputable def RMG
    (N K : ℕ) (C : Capacity K)
    [NeZero N]
    (x : Allocation N K C) : ℝ :=
  Finset.univ.inf' (by simp [Finset.univ_nonempty])
    (fun i => CNSS N K C x i)

noncomputable def VAR
    (N K : ℕ) (C : Capacity K)
    (x : Allocation N K C) : ℝ :=
  let mean := (∑ i, CNSS N K C x i) / N
  (∑ i, (CNSS N K C x i - mean) ^ 2) / N

noncomputable def DWESG
    (N K : ℕ) (C : Capacity K)
    (p : SurvivalProb N)
    (w : PrioritarianWeights N)
    (x : Allocation N K C) : ℝ :=
  ∑ i, w i * p i * CNSS N K C x i

noncomputable def VWCI
    (N K : ℕ) (C : Capacity K)
    (w : CareWeights N)
    (x : Allocation N K C) : ℝ :=
  ∑ i, w i * CNSS N K C x i

noncomputable def Gini
    (N K : ℕ) (C : Capacity K)
    (x : Allocation N K C) : ℝ :=
  let h : Fin N → ℝ := fun i => CNSS N K C x i
  let total := ∑ i, h i
  (2 * ∑ i : Fin N, ((i.val : ℝ) + 1) * h i) /
  (N * total) - (N + 1) / N

def numFrameworks : ℕ := 6
def FairnessMetric (N K : ℕ) (C : Capacity K) := Allocation N K C → ℝ

-- ============================================
-- SECTION 5: PREFERENCE PROFILES
-- ============================================

structure PreferenceProfile where
  weights : Fin numFrameworks → ℝ
  nonneg  : ∀ k, weights k ≥ 0
  sum_one : ∑ k, weights k = 1

-- ============================================
-- SECTION 6: AGENT UTILITY
-- ============================================

noncomputable def agentUtility
    (N K : ℕ) (C : Capacity K)
    (profile : PreferenceProfile)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (x : Allocation N K C) : ℝ :=
  ∑ k, profile.weights k * metrics k x

-- ============================================
-- SECTION 7: SOLO OPTIMUM
-- ============================================

def IsSoloOptimum
    (N K : ℕ) (C : Capacity K)
    (profile : PreferenceProfile)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (x : Allocation N K C) : Prop :=
  ∀ y : Allocation N K C,
    agentUtility N K C profile metrics x ≥
    agentUtility N K C profile metrics y

-- ============================================
-- SECTION 8: INCOMMENSURABILITY
-- ============================================

def Incommensurable (pA pB : PreferenceProfile) : Prop :=
  ∃ k l : Fin numFrameworks,
    pA.weights k > pA.weights l ∧
    pB.weights k < pB.weights l

lemma incommensurable_not_symm
    (pA pB : PreferenceProfile)
    (h : Incommensurable pA pB) :
    Incommensurable pB pA := by
  obtain ⟨k, l, hkl_A, hkl_B⟩ := h
  exact ⟨l, k, hkl_B, hkl_A⟩

lemma weight_pos_of_gt
    (p : PreferenceProfile)
    (k l : Fin numFrameworks)
    (h : p.weights k > p.weights l) :
    p.weights k > 0 :=
  lt_of_le_of_lt (p.nonneg l) h

lemma weight_pos_of_lt
    (p : PreferenceProfile)
    (k l : Fin numFrameworks)
    (h : p.weights k < p.weights l) :
    p.weights l > 0 :=
  lt_of_le_of_lt (p.nonneg k) h

lemma exists_pos_weight (p : PreferenceProfile) :
    ∃ k : Fin numFrameworks, p.weights k > 0 := by
  by_contra h
  push_neg at h
  have hall : ∀ k : Fin numFrameworks, p.weights k = 0 :=
    fun k => le_antisymm (h k) (p.nonneg k)
  have : ∑ k : Fin numFrameworks, p.weights k = 0 := by
    simp [hall]
  linarith [p.sum_one]

-- ============================================
-- SECTION 9: NON-DEGENERACY
-- ============================================

def NonDegenerate
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C) : Prop :=
  ¬ ∃ (x : Allocation N K C),
      ∀ (k : Fin numFrameworks) (y : Allocation N K C),
        metrics k x ≥ metrics k y

lemma nd_gives_strict_improvement
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (h_nd : NonDegenerate N K C metrics)
    (x : Allocation N K C) :
    ∃ (k : Fin numFrameworks) (z : Allocation N K C),
      metrics k z > metrics k x := by
  by_contra h
  push_neg at h
  apply h_nd
  exact ⟨x, fun k z => h k z⟩

lemma no_perfect_allocation
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (h : NonDegenerate N K C metrics) :
    ¬ ∃ (x : Allocation N K C),
        ∀ (k : Fin numFrameworks) (y : Allocation N K C),
          metrics k x ≥ metrics k y := h

-- ============================================
-- SECTION 10: DEBATE PROTOCOL
-- ============================================

structure DebateRound (N K : ℕ) (C : Capacity K) where
  propA : Allocation N K C
  propB : Allocation N K C

structure DebateProtocol (N K : ℕ) (C : Capacity K) where
  T : ℕ
  hT : 0 < T
  rounds : Fin T → DebateRound N K C
  joint : Allocation N K C

-- ============================================
-- SECTION 11: EMERGENT FAIRNESS
-- ============================================

/-- DEFINITION: Emergent Fairness
    Three conditions E1, E2, E3 must all hold.

    E1 — FEASIBILITY: x* is a valid feasible allocation
    E2 — NON-REDUCIBILITY: x* ≠ xA_solo and x* ≠ xB_solo
    E3 — CROSS IMPROVEMENT: x* beats both solo optima
         on at least one metric each agent values -/
def EmergentFairness
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C) : Prop :=
  -- E1: Feasibility (non-negativity and capacity)
  (∀ i k, proto.joint.val i k ≥ 0) ∧
  (∀ k, ∑ i, proto.joint.val i k ≤ C k) ∧
  -- E2: Non-Reducibility
  (¬ IsSoloOptimum N K C pA metrics proto.joint) ∧
  (¬ IsSoloOptimum N K C pB metrics proto.joint) ∧
  -- E3: Cross Improvement
  (∃ k : Fin numFrameworks, pA.weights k > 0 ∧
    metrics k proto.joint > metrics k xB_solo) ∧
  (∃ k : Fin numFrameworks, pB.weights k > 0 ∧
    metrics k proto.joint > metrics k xA_solo)

-- Unpacking lemmas for EmergentFairness
lemma emergent_nonneg
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ∀ i k, proto.joint.val i k ≥ 0 := h.1

lemma emergent_capacity
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ∀ k, ∑ i, proto.joint.val i k ≤ C k := h.2.1

lemma emergent_not_solo_A
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ¬ IsSoloOptimum N K C pA metrics proto.joint := h.2.2.1

lemma emergent_not_solo_B
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ¬ IsSoloOptimum N K C pB metrics proto.joint := h.2.2.2.1

lemma emergent_beats_B_solo
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ∃ k : Fin numFrameworks, pA.weights k > 0 ∧
      metrics k proto.joint > metrics k xB_solo :=
  h.2.2.2.2.1

lemma emergent_beats_A_solo
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA_solo xB_solo : Allocation N K C)
    (proto : DebateProtocol N K C)
    (h : EmergentFairness N K C metrics pA pB xA_solo xB_solo proto) :
    ∃ k : Fin numFrameworks, pB.weights k > 0 ∧
      metrics k proto.joint > metrics k xA_solo :=
  h.2.2.2.2.2

end FairnessEmergence
