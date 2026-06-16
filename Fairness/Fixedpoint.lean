/-
Copyright (c) 2026 Sayan Kumar Chaki, Antoine Gourru, Julien Velcin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayan Kumar Chaki, Antoine Gourru, Julien Velcin
-/
import Mathlib
import Fairness.definitions

/-!
# Best Response, Fixed Point, and Non-Reducibility

Uses definitions from definitions.lean:
- IsSoloOptimum, Incommensurable, NonDegenerate
- weight_pos_of_gt, weight_pos_of_lt, exists_pos_weight
- nd_gives_strict_improvement, incommensurable_not_symm
-/

namespace FairnessEmergence

-- ============================================
-- SECTION 1: CONSTRAINED BEST RESPONSE
-- ============================================

/-- Constrained best response: agent maximizes utility
    subject to respecting one of the other's metric values -/
def IsBestResponse
    (N K : ℕ) (C : Capacity K)
    (profile : PreferenceProfile)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (other : Allocation N K C)
    (x : Allocation N K C) : Prop :=
  (∀ y : Allocation N K C,
    (∃ k, metrics k y ≥ metrics k other) →
    agentUtility N K C profile metrics x ≥
    agentUtility N K C profile metrics y) ∧
  (∃ k, metrics k x ≥ metrics k other)

/-- A solo optimum is a best response to itself -/
lemma solo_is_best_response_to_self
    (N K : ℕ) (C : Capacity K)
    (profile : PreferenceProfile)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (x : Allocation N K C)
    (h : IsSoloOptimum N K C profile metrics x) :
    IsBestResponse N K C profile metrics x x := by
  constructor
  · intro y _; exact h y
  · obtain ⟨k, _⟩ := exists_pos_weight profile
    exact ⟨k, le_refl _⟩

-- ============================================
-- SECTION 2: NON-MAXIMALITY FROM NON-DEGENERACY
-- ============================================

lemma solo_not_maximal_all_metrics
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pB : PreferenceProfile)
    (h_nd : NonDegenerate N K C metrics)
    (xB : Allocation N K C)
    (h_soloB : IsSoloOptimum N K C pB metrics xB) :
    ∃ (k : Fin numFrameworks) (z : Allocation N K C),
      metrics k z > metrics k xB :=
  nd_gives_strict_improvement N K C metrics h_nd xB

-- ============================================
-- SECTION 3: UTILITY STRICT INCREASE
-- ============================================

/-- If metric k improves with positive weight and
    all other metrics weakly improve then utility
    strictly increases -/
lemma utility_strict_increase
    (N K : ℕ) (C : Capacity K)
    (profile : PreferenceProfile)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (x z : Allocation N K C)
    (k : Fin numFrameworks)
    (hk_pos : profile.weights k > 0)
    (hk_better : metrics k z > metrics k x)
    (hj_ge : ∀ j : Fin numFrameworks,
      j ≠ k → metrics j z ≥ metrics j x) :
    agentUtility N K C profile metrics z >
    agentUtility N K C profile metrics x := by
  unfold agentUtility
  apply Finset.sum_lt_sum
  · intro j _
    apply mul_le_mul_of_nonneg_left _ (profile.nonneg j)
    by_cases hjk : j = k
    · subst hjk; exact le_of_lt hk_better
    · exact hj_ge j hjk
  · exact ⟨k, Finset.mem_univ k,
      mul_lt_mul_of_pos_left hk_better hk_pos⟩

-- ============================================
-- SECTION 4: CONSTRAINED ≠ SOLO
-- ============================================

/-- KEY LEMMA: constrained best response is not
    a solo optimum under incommensurability -/
lemma constrained_ne_solo
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (h_inc : Incommensurable pA pB)
    (h_nd : NonDegenerate N K C metrics)
    (xA xB : Allocation N K C)
    (h_br : IsBestResponse N K C pA metrics xB xA)
    (h_soloB : IsSoloOptimum N K C pB metrics xB) :
    ¬ IsSoloOptimum N K C pA metrics xA := by
  intro h_soloA
  obtain ⟨m, z, hmz⟩ :=
    solo_not_maximal_all_metrics N K C metrics pB
      h_nd xB h_soloB
  have hz_constr : ∃ j, metrics j z ≥ metrics j xB :=
    ⟨m, le_of_lt hmz⟩
  obtain ⟨h_br_max, _⟩ := h_br
  have hxA_z := h_br_max z hz_constr
  apply h_nd
  use xA
  intro k y
  sorry

-- ============================================
-- SECTION 5: NASH EQUILIBRIUM FIXED POINT
-- ============================================

def IsFixedPoint
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA xB : Allocation N K C) : Prop :=
  IsBestResponse N K C pA metrics xB xA ∧
  IsBestResponse N K C pB metrics xA xB

lemma fp_A_cannot_improve
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA xB : Allocation N K C)
    (h : IsFixedPoint N K C metrics pA pB xA xB)
    (y : Allocation N K C)
    (hy : ∃ k, metrics k y ≥ metrics k xB) :
    agentUtility N K C pA metrics xA ≥
    agentUtility N K C pA metrics y :=
  h.1.1 y hy

lemma fp_B_cannot_improve
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA xB : Allocation N K C)
    (h : IsFixedPoint N K C metrics pA pB xA xB)
    (y : Allocation N K C)
    (hy : ∃ k, metrics k y ≥ metrics k xA) :
    agentUtility N K C pB metrics xB ≥
    agentUtility N K C pB metrics y :=
  h.2.1 y hy

-- ============================================
-- SECTION 6: KAKUTANI (AXIOMATIZED)
-- ============================================

/-- AXIOM: Fixed Point Existence (Kakutani, 1941).
    Allocation space is compact convex, best response
    is nonempty convex valued and upper hemicontinuous,
    so a fixed point exists. -/
axiom fixed_point_exists
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile) :
    ∃ xA xB : Allocation N K C,
      IsFixedPoint N K C metrics pA pB xA xB

-- ============================================
-- SECTION 7: NON-REDUCIBILITY FROM FIXED POINT
-- ============================================

lemma fp_xA_not_solo
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA xB : Allocation N K C)
    (h_fp : IsFixedPoint N K C metrics pA pB xA xB)
    (h_inc : Incommensurable pA pB)
    (h_nd : NonDegenerate N K C metrics)
    (h_soloB : IsSoloOptimum N K C pB metrics xB) :
    ¬ IsSoloOptimum N K C pA metrics xA :=
  constrained_ne_solo N K C metrics pA pB
    h_inc h_nd xA xB h_fp.1 h_soloB

lemma fp_xB_not_solo
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (xA xB : Allocation N K C)
    (h_fp : IsFixedPoint N K C metrics pA pB xA xB)
    (h_inc : Incommensurable pA pB)
    (h_nd : NonDegenerate N K C metrics)
    (h_soloA : IsSoloOptimum N K C pA metrics xA) :
    ¬ IsSoloOptimum N K C pB metrics xB :=
  constrained_ne_solo N K C metrics pB pA
    (incommensurable_not_symm pA pB h_inc)
    h_nd xB xA h_fp.2 h_soloA

end FairnessEmergence
