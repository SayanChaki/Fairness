/-
Copyright (c) 2026 Sayan Kumar Chaki, Antoine Gourru, Julien Velcin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayan Kumar Chaki, Antoine Gourru, Julien Velcin
-/
import Mathlib
import Fairness.definitions

/-!
# Balanced Emergent Fairness (min-max / leximin formulation)

This file gives the revised definition of emergent fairness
based on BALANCE rather than the weaker "beats both solo
optima on some metric".

## The idea
Each agent i has a distinguished metric f_i. Its solo optimum
x_i is high on f_i but low on the others. The debate output x*
should be BALANCED: good on every metric simultaneously, not
maximal on any single one.

## Core objects
- g_j(x) = f_j(x) / f_j^max         normalized score in [0,1]
- beta(x) = min_j g_j(x)            the floor (worst metric)
- beta_opt = max_x beta(x)          best achievable floor (maximin)

## Emergence (three conditions)
- E1 floor lifted:  beta(x*) > max_i beta(x_i)
- E2 near-optimal:  beta(x*) >= beta_opt - eps
- E3 no waste:      x* is Pareto-efficient

The whole thing generalizes to n agents automatically because
beta is a min over all metrics.
-/

namespace FairnessEmergence

/-- Fin numFrameworks is nonempty (numFrameworks = 6). -/
lemma univ_fin_nonempty :
    (Finset.univ : Finset (Fin numFrameworks)).Nonempty :=
  Finset.univ_nonempty_iff.mpr ⟨⟨0, by unfold numFrameworks; norm_num⟩⟩

-- ============================================
-- SECTION 1: NORMALIZED SCORES
-- ============================================

/-- The attainable ceiling of metric j: the best value
    f_j takes over all feasible allocations. Provided as
    a parameter (its existence follows from compactness of
    the allocation space via Weierstrass; we take it as
    given data here). -/
def MetricCeiling (N K : ℕ) (C : Capacity K) := Fin numFrameworks → ℝ

/-- The normalized score g_j(x) = f_j(x) / f_j^max.
    Measures the FRACTION of the attainable optimum that
    allocation x achieves on metric j. Lives in [0,1]
    when the ceiling is a true maximum and f_j ≥ 0. -/
noncomputable def normScore
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (j : Fin numFrameworks)
    (x : Allocation N K C) : ℝ :=
  metrics j x / ceil j

/-- A ceiling is VALID if it is positive and genuinely
    bounds every allocation's metric value. -/
def ValidCeiling
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C) : Prop :=
  (∀ j, ceil j > 0) ∧
  (∀ j x, metrics j x ≤ ceil j)

/-- Under a valid ceiling, every normalized score is ≤ 1 -/
lemma normScore_le_one
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (h_valid : ValidCeiling N K C metrics ceil)
    (j : Fin numFrameworks)
    (x : Allocation N K C) :
    normScore N K C metrics ceil j x ≤ 1 := by
  unfold normScore
  rw [div_le_one (h_valid.1 j)]
  exact h_valid.2 j x

-- ============================================
-- SECTION 2: THE FLOOR (BALANCE SCORE)
-- ============================================

/-- The floor beta(x) = min_j g_j(x): the weakest
    normalized metric of allocation x. An allocation is
    only as balanced as its worst-treated metric. -/
noncomputable def floor
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (x : Allocation N K C) : ℝ :=
  Finset.univ.inf' univ_fin_nonempty
    (fun j => normScore N K C metrics ceil j x)

/-- The floor is a lower bound on every normalized score -/
lemma floor_le_normScore
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (x : Allocation N K C)
    (j : Fin numFrameworks) :
    floor N K C metrics ceil x ≤
    normScore N K C metrics ceil j x := by
  unfold floor
  exact Finset.inf'_le _ (Finset.mem_univ j)

/-- If every normalized score is ≥ c then the floor is ≥ c -/
lemma le_floor
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (x : Allocation N K C)
    (c : ℝ)
    (h : ∀ j, c ≤ normScore N K C metrics ceil j x) :
    c ≤ floor N K C metrics ceil x := by
  unfold floor
  exact Finset.le_inf' _ _ (fun j _ => h j)

-- ============================================
-- SECTION 3: THE MAXIMIN OPTIMUM beta_opt
-- ============================================

/-- beta_opt is the best achievable floor: the maximin value.
    Provided as data with its defining properties, since
    its existence requires compactness (Weierstrass). -/
structure MaximinOptimum
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C) where
  -- the optimal floor value
  value : ℝ
  -- it is attained by some allocation
  witness : Allocation N K C
  attains : floor N K C metrics ceil witness = value
  -- it is the maximum: no allocation exceeds it
  maximal : ∀ x, floor N K C metrics ceil x ≤ value

/-- beta_opt upper-bounds every allocation's floor -/
lemma floor_le_betaOpt
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (x : Allocation N K C) :
    floor N K C metrics ceil x ≤ bopt.value :=
  bopt.maximal x

-- ============================================
-- SECTION 4: PARETO EFFICIENCY
-- ============================================

/-- y dominates x if y is ≥ x on every normalized metric
    and strictly greater on at least one. -/
def Dominates
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (y x : Allocation N K C) : Prop :=
  (∀ j, normScore N K C metrics ceil j x ≤
        normScore N K C metrics ceil j y) ∧
  (∃ k, normScore N K C metrics ceil k x <
        normScore N K C metrics ceil k y)

/-- x is Pareto-efficient if nothing dominates it.
    This is the "no waste" guard: no metric can be raised
    without lowering another. -/
def ParetoEfficientAlloc
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (x : Allocation N K C) : Prop :=
  ¬ ∃ y, Dominates N K C metrics ceil y x

-- ============================================
-- SECTION 5: SOLO FLOORS
-- ============================================

/-- The best floor achievable by any single agent acting
    alone: max over the n solo allocations of their floors. -/
noncomputable def bestSoloFloor
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (solos : Fin numFrameworks → Allocation N K C) : ℝ :=
  Finset.univ.sup' univ_fin_nonempty
    (fun i => floor N K C metrics ceil (solos i))

/-- The best solo floor is ≥ each individual solo floor -/
lemma soloFloor_le_bestSoloFloor
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (solos : Fin numFrameworks → Allocation N K C)
    (i : Fin numFrameworks) :
    floor N K C metrics ceil (solos i) ≤
    bestSoloFloor N K C metrics ceil solos := by
  unfold bestSoloFloor
  exact Finset.le_sup' (fun i => floor N K C metrics ceil (solos i)) (Finset.mem_univ i)

-- ============================================
-- SECTION 6: EMERGENT FAIRNESS (BALANCED)
-- ============================================

/-- DEFINITION: Balanced Emergent Fairness.

    The debate output x* exhibits emergent fairness if:

    E1 (floor lifted):  beta(x*) > max_i beta(x_i)
        strictly more balanced than any solo allocation

    E2 (near-optimal):  beta(x*) >= beta_opt - eps
        genuinely close to the best achievable balance

    E3 (no waste):      x* is Pareto-efficient
        no metric needlessly sacrificed -/
def EmergentFairnessBalanced
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ)
    (xstar : Allocation N K C) : Prop :=
  -- E1: floor strictly lifted above any solo allocation
  (floor N K C metrics ceil xstar >
    bestSoloFloor N K C metrics ceil solos) ∧
  -- E2: floor near the maximin optimum
  (floor N K C metrics ceil xstar ≥ bopt.value - eps) ∧
  -- E3: Pareto-efficient (no waste)
  (ParetoEfficientAlloc N K C metrics ceil xstar)

-- Unpacking lemmas
lemma emergent_floor_lifted
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ) (xstar : Allocation N K C)
    (h : EmergentFairnessBalanced N K C metrics ceil
           bopt solos eps xstar) :
    floor N K C metrics ceil xstar >
    bestSoloFloor N K C metrics ceil solos := h.1

lemma emergent_near_optimal
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ) (xstar : Allocation N K C)
    (h : EmergentFairnessBalanced N K C metrics ceil
           bopt solos eps xstar) :
    floor N K C metrics ceil xstar ≥ bopt.value - eps := h.2.1

lemma emergent_no_waste
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ) (xstar : Allocation N K C)
    (h : EmergentFairnessBalanced N K C metrics ceil
           bopt solos eps xstar) :
    ParetoEfficientAlloc N K C metrics ceil xstar := h.2.2


-- ============================================
-- PART 2: STRICT GAP (DERIVED)
-- ============================================

def SoloCraters
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C) : Prop :=
  ∀ i, ∃ m, normScore N K C metrics ceil m (solos i) < bopt.value

lemma soloFloor_lt_betaOpt
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (h_crater : SoloCraters N K C metrics ceil bopt solos)
    (i : Fin numFrameworks) :
    floor N K C metrics ceil (solos i) < bopt.value := by
  obtain ⟨m, hm⟩ := h_crater i
  calc floor N K C metrics ceil (solos i)
      ≤ normScore N K C metrics ceil m (solos i) :=
        floor_le_normScore N K C metrics ceil (solos i) m
    _ < bopt.value := hm

theorem strictGap_derived
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (h_crater : SoloCraters N K C metrics ceil bopt solos) :
    bestSoloFloor N K C metrics ceil solos < bopt.value := by
  unfold bestSoloFloor
  rw [Finset.sup'_lt_iff univ_fin_nonempty]
  intro i _
  exact soloFloor_lt_betaOpt N K C metrics ceil bopt solos h_crater i

-- ============================================
-- PART 2b: DISCHARGING SoloCraters
-- ============================================

lemma normScore_lt_of_raw_lt
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (h_valid : ValidCeiling N K C metrics ceil)
    (bopt : MaximinOptimum N K C metrics ceil)
    (m : Fin numFrameworks)
    (x : Allocation N K C)
    (h_raw : metrics m x < bopt.value * ceil m) :
    normScore N K C metrics ceil m x < bopt.value := by
  unfold normScore
  rw [div_lt_iff₀ (h_valid.1 m)]
  exact h_raw

theorem soloCraters_of_pairwise
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (h_valid : ValidCeiling N K C metrics ceil)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (h_raw_crater : ∀ i, ∃ m,
      metrics m (solos i) < bopt.value * ceil m) :
    SoloCraters N K C metrics ceil bopt solos := by
  intro i
  obtain ⟨m, hm⟩ := h_raw_crater i
  exact ⟨m, normScore_lt_of_raw_lt N K C metrics ceil
    h_valid bopt m (solos i) hm⟩

-- ============================================
-- PART 3: E3 — NO WASTE (assumed)
-- ============================================

def B3_Efficiency
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (xstar : Allocation N K C) : Prop :=
  ParetoEfficientAlloc N K C metrics ceil xstar

theorem E3_no_waste
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (xstar : Allocation N K C)
    (h_B3 : B3_Efficiency N K C metrics ceil xstar) :
    ParetoEfficientAlloc N K C metrics ceil xstar :=
  h_B3

-- ============================================
-- PART 4: E1 — FLOOR LIFTED
-- ============================================

theorem E1_floor_lifted
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ)
    (xstar : Allocation N K C)
    (h_reach : floor N K C metrics ceil xstar ≥ bopt.value - eps)
    (h_eps : eps < bopt.value - bestSoloFloor N K C metrics ceil solos) :
    floor N K C metrics ceil xstar >
    bestSoloFloor N K C metrics ceil solos := by
  calc bestSoloFloor N K C metrics ceil solos
      < bopt.value - eps := by linarith
    _ ≤ floor N K C metrics ceil xstar := h_reach
-- ============================================
-- PART 5: E2 — NEAR-OPTIMAL (from reachability)
-- ============================================

/-- E2 PROVED: the debate floor is near the maximin optimum.
    This is exactly the reachability hypothesis. -/
theorem E2_near_optimal
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (eps : ℝ)
    (xstar : Allocation N K C)
    (h_reach : floor N K C metrics ceil xstar ≥ bopt.value - eps) :
    floor N K C metrics ceil xstar ≥ bopt.value - eps :=
  h_reach

-- ============================================
-- PART 6: MAIN THEOREM — BALANCED EMERGENCE
-- ============================================

/-- MAIN THEOREM: Balanced Emergent Fairness.

    Given:
    - reachability: the debate reaches the maximin floor (B1)
    - strict gap via SoloCraters: every solo allocation craters
    - small tolerance: eps below the gap
    - efficiency: x* is Pareto-efficient (B3)

    Then x* satisfies all three emergence conditions:
    E1 floor lifted, E2 near-optimal, E3 no waste.

    This is the complete balanced emergence theorem. -/
theorem emergent_fairness_balanced
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (ceil : MetricCeiling N K C)
    (bopt : MaximinOptimum N K C metrics ceil)
    (solos : Fin numFrameworks → Allocation N K C)
    (eps : ℝ)
    (xstar : Allocation N K C)
    (h_reach : floor N K C metrics ceil xstar ≥ bopt.value - eps)
    (h_crater : SoloCraters N K C metrics ceil bopt solos)
    (h_eps : eps < bopt.value - bestSoloFloor N K C metrics ceil solos)
    (h_B3 : B3_Efficiency N K C metrics ceil xstar) :
    EmergentFairnessBalanced N K C metrics ceil bopt solos eps xstar := by
  refine ⟨?_, ?_, ?_⟩
  · -- E1: floor lifted
    exact E1_floor_lifted N K C metrics ceil bopt solos eps xstar
      h_reach h_eps
  · -- E2: near-optimal
    exact h_reach
  · -- E3: no waste
    exact h_B3
end FairnessEmergence
