import Mathlib.Data.ENNReal.Basic

/-!
# First-hitting and persistence times

This module gives the generic extended-nonnegative-time interfaces used for
thermalization observables.  It follows the operational threshold convention
in Wang--Fu--Zhang--Zhao, arXiv:1903.09502v2, p. 4: a first hit is the infimum
of strictly positive event times, and is `⊤` when no event occurs.  The
persistence variant requires the event throughout the closed interval
`[t, t + L]`; see the campaign roadmap, Section 6.

These order-theoretic facts do not assert that an infimum is attained or that
the event occurs.
-/

namespace ArchonPhysics.HittingTime

noncomputable section

/-- Strictly positive times at which the event holds. -/
def hittingTimes (A : ENNReal → Prop) : Set ENNReal :=
  {t | 0 < t ∧ A t}

/-- The first strictly positive event time, with `⊤` for an empty event set. -/
def firstHittingTime (A : ENNReal → Prop) : ENNReal :=
  sInf (hittingTimes A)

/-- The event holds continuously from `t` through the duration `L`. -/
def PersistsFor (A : ENNReal → Prop) (t L : ENNReal) : Prop :=
  ∀ s, t ≤ s → s ≤ t + L → A s

/-- Strictly positive start times at which the event persists for `L`. -/
def persistenceTimes (A : ENNReal → Prop) (L : ENNReal) : Set ENNReal :=
  {u | 0 < u ∧ PersistsFor A u L}

/-- The first strictly positive start time at which the event persists for `L`. -/
def persistenceTime (A : ENNReal → Prop) (L : ENNReal) : ENNReal :=
  sInf (persistenceTimes A L)

/-- An event that never holds has first hitting time `⊤`. -/
theorem firstHittingTime_empty :
    firstHittingTime (fun _ : ENNReal => False) = ⊤ := by
  simp [firstHittingTime, hittingTimes]

/-- Every strictly positive event time bounds the first hitting time from above. -/
theorem firstHittingTime_le_of_mem (A : ENNReal → Prop) {t : ENNReal}
    (ht : t ∈ hittingTimes A) : firstHittingTime A ≤ t := by
  exact sInf_le ht

/-- Enlarging an event can only make its first hitting time earlier. -/
theorem firstHittingTime_mono (A B : ENNReal → Prop) (hAB : ∀ t, A t → B t) :
    firstHittingTime B ≤ firstHittingTime A := by
  apply sInf_le_sInf
  intro t ht
  exact ⟨ht.1, hAB t ht.2⟩

/-- The defining formulae for strictly positive hitting times. -/
theorem hitting_spec (A : ENNReal → Prop) :
    hittingTimes A = {t | 0 < t ∧ A t} ∧
      firstHittingTime A = sInf (hittingTimes A) := by
  exact ⟨rfl, rfl⟩

/-- No strictly positive event can occur strictly before the first hitting time. -/
theorem not_event_before_firstHittingTime (A : ENNReal → Prop) (t : ENNReal)
    (ht : 0 < t) (hbefore : t < firstHittingTime A) : ¬ A t := by
  intro hAt
  exact (not_lt_of_ge (firstHittingTime_le_of_mem A ⟨ht, hAt⟩)) hbefore

/-- The defining formulae for duration-indexed persistence times. -/
theorem persistence_spec (A : ENNReal → Prop) (t L : ENNReal) :
    (PersistsFor A t L ↔ ∀ s, t ≤ s → s ≤ t + L → A s) ∧
      persistenceTimes A L = {u | 0 < u ∧ PersistsFor A u L} ∧
        persistenceTime A L = sInf (persistenceTimes A L) := by
  exact ⟨Iff.rfl, rfl, rfl⟩

end

end ArchonPhysics.HittingTime
