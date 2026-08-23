import Mathlib
import ArchonPhysics
import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic

/-! First-hitting and persistence-time interfaces for approximate equipartition. -/

namespace ArchonPhysics.Generated.HittingTime

noncomputable section

/-- The positive extended times at which an observable satisfies a target predicate. -/
def equilibrationTimes (P : ENNReal → Prop) : Set ENNReal :=
  {t | 0 < t ∧ P t}

/-- The first hitting time, using `⊤` as the infimum of an empty time set. -/
def equilibrationHittingTime (P : ENNReal → Prop) : ENNReal :=
  sInf (equilibrationTimes P)

/-- Persistence of a property from time `t` for a duration `δ`. -/
def PersistsFor (P : ENNReal → Prop) (t duration : ENNReal) : Prop :=
  ∀ s, t ≤ s → s ≤ t + duration → P s

/-- Basic order and membership consequences of the extended-real first hitting time. -/
theorem hitting_time_physics_formalization_target
    (P : ENNReal → Prop) (hnonempty : (equilibrationTimes P).Nonempty)
    {t : ENNReal} (ht : t ∈ equilibrationTimes P) :
    equilibrationHittingTime P ≤ t ∧ P t := by
  constructor
  · exact sInf_le ht
  · exact ht.2

end

end ArchonPhysics.Generated.HittingTime
