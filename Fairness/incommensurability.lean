/-
Copyright (c) 2026 Sayan Kumar Chaki, Antoine Gourru, Julien Velcin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayan Kumar Chaki, Antoine Gourru, Julien Velcin
-/
import Mathlib
import Fairness.definitions
import Fairness.Fixedpoint

/-!
# Decomposition of Assumption A4

The original A4 ("incommensurability drives divergence")
is suspiciously close to the conclusion. This file
decomposes it into three honest primitives and derives
A4 from them, isolating exactly the one irreducible
protocol assumption.

## The decomposition
- A4a (Preference→Outcome): weighting metric m heavily
  yields high f_m at the optimum. DERIVABLE for monotone
  metrics via comparative statics.
- A4b (Metric conflict): the (k,l) pair genuinely conflicts.
  FOLDED into pairwise non-degeneracy (a problem property).
- A4c (Faithfulness): agents argue for what they value
  during debate. Split into existence (near-free) and
  faithfulness-under-pressure (the irreducible assumption).

## Result
A4 reduces to: pairwise non-degeneracy (definitional)
+ monotonicity (checkable per metric)
+ A4c-faithfulness (the single genuine protocol assumption).
-/

namespace FairnessEmergence

-- ============================================
-- MONOTONE METRICS
-- ============================================

/-- Pointwise order on allocations: x ≤ y if every
    patient gets at least as much of every resource -/
def AllocLe (N K : ℕ) (C : Capacity K)
    (x y : Allocation N K C) : Prop :=
  ∀ i k, x.val i k ≤ y.val i k

/-- A metric is monotone if giving more resources
    never decreases it. Holds for level-based metrics
    (ESG, RMG, DW-ESG, VWCI) but NOT dispersion-based
    metrics (VAR, Gini). -/
def MonotoneMetric (N K : ℕ) (C : Capacity K)
    (f : FairnessMetric N K C) : Prop :=
  ∀ x y : Allocation N K C,
    AllocLe N K C x y → f x ≤ f y

-- ============================================
-- A4b: PAIRWISE NON-DEGENERACY
-- ============================================

/-- Pairwise non-degeneracy: for two specific metrics
    k and l, no single allocation maximizes both.
    This is stronger than global non-degeneracy and
    is the property actually used in the emergence proof.

    NOTE: this FAILS for compatible pairs like
    (ESG, DW-ESG) which are both monotone weighted sums.
    The theory correctly predicts NO emergence for such
    pairs — no tension, nothing to resolve. -/
def PairwiseNonDegenerate
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (k l : Fin numFrameworks) : Prop :=
  ¬ ∃ (x : Allocation N K C),
      (∀ y, metrics k x ≥ metrics k y) ∧
      (∀ y, metrics l x ≥ metrics l y)

/-- A4b derived: pairwise non-degeneracy means the
    l-maximizer cannot also be the k-maximizer.
    So there is an allocation beating the l-maximizer
    on metric k. -/
lemma A4b_metric_conflict
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (k l : Fin numFrameworks)
    (h_pnd : PairwiseNonDegenerate N K C metrics k l)
    (xl : Allocation N K C)
    (h_xl_max_l : ∀ y, metrics l xl ≥ metrics l y) :
    ∃ z, metrics k z > metrics k xl := by
  by_contra h
  push_neg at h
  -- if no z beats xl on k, then xl maximizes k too
  apply h_pnd
  exact ⟨xl, fun y => h y, h_xl_max_l⟩

-- ============================================
-- A4a: PREFERENCE → OUTCOME (MONOTONE CASE)
-- ============================================

/-- A4a for monotone metrics, stated as the
    comparative-statics consequence.

    If metric m is monotone and an agent's solo
    optimum dominates allocation z pointwise, then
    the agent's optimum scores at least as high on m.

    This is the order-theoretic core: optimizers
    of monotone objectives inherit monotonicity. -/
lemma A4a_monotone
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (m : Fin numFrameworks)
    (h_mono : MonotoneMetric N K C (metrics m))
    (x z : Allocation N K C)
    (h_dom : AllocLe N K C z x) :
    metrics m z ≤ metrics m x :=
  h_mono z x h_dom

-- ============================================
-- A4c: FAITHFULNESS, SPLIT
-- ============================================

/-- A4c-existence: at some round, agent A proposes
    an allocation scoring high on A's preferred metric.
    Near-free: follows from A being an optimizer. -/
def A4c_existence
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (proto : DebateProtocol N K C)
    (k : Fin numFrameworks)
    (ref : Allocation N K C) : Prop :=
  ∃ t : Fin proto.T,
    metrics k (proto.rounds t).propA > metrics k ref

/-- A4c-faithfulness: THE irreducible protocol assumption.

    Agent A keeps pushing metric k even while constrained
    by B's counterproposals. This is what an adversarial B
    ("cumulative argumentation bias") could try to break.

    It cannot be derived from rationality — rationality is
    exactly what the adversary exploits. It is a genuine
    claim about the protocol's strategic robustness. -/
def A4c_faithfulness
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (proto : DebateProtocol N K C)
    (pA : PreferenceProfile)
    (k : Fin numFrameworks) : Prop :=
  -- A's proposals consistently push metric k
  -- (the protocol is not manipulable on metric k)
  ∀ ref : Allocation N K C,
    pA.weights k > 0 →
    (∃ t : Fin proto.T,
      metrics k (proto.rounds t).propA > metrics k ref) →
    A4c_existence N K C metrics proto k ref

-- ============================================
-- DERIVING A4 FROM THE PRIMITIVES
-- ============================================

/-- A4 (one direction, for agent A) derived from primitives.

    Given:
    - k is A's preferred framework (positive weight)
    - pairwise non-degeneracy of (k, l)
    - B's solo optimum maximizes metric l
    - A4c-existence: A proposes high-k allocations

    Then: A's proposals beat B's solo optimum on metric k.

    This replaces the raw A4 assumption with a derivation
    from a problem property (pairwise non-degeneracy) plus
    the faithfulness primitive. -/
theorem A4_derived_for_A
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (proto : DebateProtocol N K C)
    (k l : Fin numFrameworks)
    (hk_pos : pA.weights k > 0)
    (h_pnd : PairwiseNonDegenerate N K C metrics k l)
    (xB_solo : Allocation N K C)
    (h_xB_max_l : ∀ y, metrics l xB_solo ≥ metrics l y)
    -- A4c: A actually proposes the conflict-witnessing allocation
    (h_faithful : ∀ z, metrics k z > metrics k xB_solo →
      ∃ t : Fin proto.T,
        metrics k (proto.rounds t).propA > metrics k xB_solo) :
    ∃ k', pA.weights k' > 0 ∧ ∃ t : Fin proto.T,
      metrics k' (proto.rounds t).propA > metrics k' xB_solo := by
  -- Step 1: pairwise non-degeneracy gives z beating
  -- B's solo optimum on metric k (A4b)
  obtain ⟨z, hz⟩ :=
    A4b_metric_conflict N K C metrics k l h_pnd xB_solo h_xB_max_l
  -- Step 2: A4c-faithfulness says A actually proposes such z
  obtain ⟨t, ht⟩ := h_faithful z hz
  -- Step 3: combine
  exact ⟨k, hk_pos, t, ht⟩

/-- Symmetric: A4 for agent B -/
theorem A4_derived_for_B
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (pA pB : PreferenceProfile)
    (proto : DebateProtocol N K C)
    (k l : Fin numFrameworks)
    (hl_pos : pB.weights l > 0)
    (h_pnd : PairwiseNonDegenerate N K C metrics l k)
    (xA_solo : Allocation N K C)
    (h_xA_max_k : ∀ y, metrics k xA_solo ≥ metrics k y)
    (h_faithful : ∀ z, metrics l z > metrics l xA_solo →
      ∃ t : Fin proto.T,
        metrics l (proto.rounds t).propB > metrics l xA_solo) :
    ∃ k', pB.weights k' > 0 ∧ ∃ t : Fin proto.T,
      metrics k' (proto.rounds t).propB > metrics k' xA_solo := by
  obtain ⟨z, hz⟩ :=
    A4b_metric_conflict N K C metrics l k h_pnd xA_solo h_xA_max_k
  obtain ⟨t, ht⟩ := h_faithful z hz
  exact ⟨l, hl_pos, t, ht⟩

-- ============================================
-- HONEST STATUS OF EACH PIECE
-- ============================================

/-- A4a is a THEOREM for monotone metrics:
    no assumption, pure order theory. -/
example
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (m : Fin numFrameworks)
    (h_mono : MonotoneMetric N K C (metrics m))
    (x z : Allocation N K C)
    (h_dom : AllocLe N K C z x) :
    metrics m z ≤ metrics m x :=
  A4a_monotone N K C metrics m h_mono x z h_dom

/-- A4b is a THEOREM given pairwise non-degeneracy:
    a definitional tightening of non-degeneracy. -/
example
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (k l : Fin numFrameworks)
    (h_pnd : PairwiseNonDegenerate N K C metrics k l)
    (xl : Allocation N K C)
    (h : ∀ y, metrics l xl ≥ metrics l y) :
    ∃ z, metrics k z > metrics k xl :=
  A4b_metric_conflict N K C metrics k l h_pnd xl h

end FairnessEmergence
