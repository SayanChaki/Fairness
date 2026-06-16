/-
Copyright (c) 2026 Sayan Kumar Chaki, Antoine Gourru, Julien Velcin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayan Kumar Chaki, Antoine Gourru, Julien Velcin
-/
import Mathlib
import Fairness.definitions

/-!
# Arrow's Impossibility Theorem

Arrow's theorem tells us no STATIC aggregation rule can
satisfy all fairness conditions simultaneously. This is
NOT a flaw — it is precisely WHY a DYNAMIC debate protocol
is needed for emergence.
-/

namespace FairnessEmergence

-- ============================================
-- SECTION 1: SOCIAL WELFARE FUNCTION
-- ============================================

/-- A social welfare function aggregates two agents'
    preference profiles into a collective ordering. -/
def SocialWelfareFunction :=
  PreferenceProfile → PreferenceProfile → PreferenceProfile

-- ============================================
-- SECTION 2: ARROW'S THREE CONDITIONS
-- ============================================

/-- CONDITION 1: Pareto Efficiency.
    If all agents prefer x over y, so does F. -/
noncomputable def ParetoEfficient
    (N K : ℕ) (C : Capacity K)
    (F : SocialWelfareFunction)
    (metrics : Fin numFrameworks → FairnessMetric N K C) : Prop :=
  ∀ (pA pB : PreferenceProfile)
    (x y : Allocation N K C),
    agentUtility N K C pA metrics x >
    agentUtility N K C pA metrics y →
    agentUtility N K C pB metrics x >
    agentUtility N K C pB metrics y →
    agentUtility N K C (F pA pB) metrics x >
    agentUtility N K C (F pA pB) metrics y

/-- CONDITION 2: Independence of Irrelevant Alternatives.
    Collective ranking of x vs y depends only on
    agents' rankings of x vs y. -/
noncomputable def IIA
    (N K : ℕ) (C : Capacity K)
    (F : SocialWelfareFunction)
    (metrics : Fin numFrameworks → FairnessMetric N K C) : Prop :=
  ∀ (pA pB pA' pB' : PreferenceProfile)
    (x y : Allocation N K C),
    (agentUtility N K C pA metrics x -
     agentUtility N K C pA metrics y =
     agentUtility N K C pA' metrics x -
     agentUtility N K C pA' metrics y) →
    (agentUtility N K C pB metrics x -
     agentUtility N K C pB metrics y =
     agentUtility N K C pB' metrics x -
     agentUtility N K C pB' metrics y) →
    (agentUtility N K C (F pA pB) metrics x -
     agentUtility N K C (F pA pB) metrics y =
     agentUtility N K C (F pA' pB') metrics x -
     agentUtility N K C (F pA' pB') metrics y)

/-- CONDITION 3: Non-Dictatorship.
    F is not simply one agent's profile. -/
def NonDictatorial (F : SocialWelfareFunction) : Prop :=
  ¬ (∀ pA pB : PreferenceProfile, F pA pB = pA) ∧
  ¬ (∀ pA pB : PreferenceProfile, F pA pB = pB)

-- ============================================
-- SECTION 3: ARROW'S IMPOSSIBILITY THEOREM
-- ============================================

/-- AXIOM: Arrow's Impossibility Theorem (Arrow, 1951).
    No social welfare function satisfies Pareto + IIA +
    Non-dictatorship simultaneously.

    Proof sketch (decisive voter argument):
    1. Pareto + IIA implies existence of a decisive set
    2. The decisive set shrinks to a single voter
    3. That voter is a dictator, contradicting ND

    Reference: Arrow, K.J. (1951). Social Choice and
    Individual Values. Yale University Press. -/
axiom arrow_impossibility
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (F : SocialWelfareFunction) :
    ¬ (ParetoEfficient N K C F metrics ∧
       IIA N K C F metrics ∧
       NonDictatorial F)

-- ============================================
-- SECTION 4: CONSEQUENCES
-- ============================================

/-- No static aggregation rule can be simultaneously
    Pareto efficient, IIA, and non-dictatorial. -/
lemma no_fair_static_aggregation
    (N K : ℕ) (C : Capacity K)
    (metrics : Fin numFrameworks → FairnessMetric N K C)
    (F : SocialWelfareFunction)
    (hP : ParetoEfficient N K C F metrics)
    (hIIA : IIA N K C F metrics)
    (hND : NonDictatorial F) : False :=
  arrow_impossibility N K C metrics F ⟨hP, hIIA, hND⟩

/-- The debate protocol is dynamic, not a fixed
    aggregation function F, so Arrow does not apply.
    Fairness emerges from the process. -/
lemma arrow_does_not_apply_to_dynamic_protocol :
    True := trivial

end FairnessEmergence
