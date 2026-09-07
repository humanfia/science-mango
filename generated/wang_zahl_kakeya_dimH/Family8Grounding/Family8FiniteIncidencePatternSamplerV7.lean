import Family8Grounding.Family8FiniteProbabilityCeilRoundingV1
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Family8FiniteIncidencePatternSamplerV7

noncomputable section

/-!
# Finite incidence-pattern sampling of a probability law

A finite measurable event family turns each point into a finite
proposition-valued incidence pattern.  Push the probability measure to the
finite pattern type, apply deterministic ceiling rounding, and choose one
point in every sampled fibre.  The resulting literal finite sample has at
least the requested scale and controls all event counts simultaneously.
-/

variable {Omega test : Type*} [MeasurableSpace Omega]
  [Fintype test] [DecidableEq test]

abbrev Pattern (test : Type*) := test -> Prop

structure MeasurableEventFamily (Omega test : Type*)
    [MeasurableSpace Omega] where
  event : test -> Set Omega
  measurable_event : forall i, MeasurableSet (event i)

namespace MeasurableEventFamily

variable (F : MeasurableEventFamily Omega test)
  (mu : Measure Omega) [IsProbabilityMeasure mu]

def incidencePattern (x : Omega) (i : test) : Prop :=
  x ∈ F.event i

theorem measurable_incidencePattern :
    Measurable F.incidencePattern := by
  rw [measurable_pi_iff]
  intro i
  simpa [incidencePattern] using
    (measurable_mem.mpr (F.measurable_event i))

def incidencePatternLaw : Measure (Pattern test) :=
  mu.map F.incidencePattern

noncomputable instance incidencePatternLaw_isProbability :
    IsProbabilityMeasure (F.incidencePatternLaw mu) :=
  Measure.isProbabilityMeasure_map
    F.measurable_incidencePattern.aemeasurable

def truePatterns (i : test) : Finset (Pattern test) :=
  @Finset.filter (Pattern test) (fun p => p i)
    (fun p => Classical.propDecidable (p i)) Finset.univ

theorem preimage_truePatterns (i : test) :
    F.incidencePattern ⁻¹'
        (truePatterns (test := test) i : Set (Pattern test)) =
      F.event i := by
  ext x
  simp [truePatterns, incidencePattern]

theorem incidencePatternLaw_real_truePatterns (i : test) :
    (F.incidencePatternLaw mu).real
        (truePatterns (test := test) i : Set (Pattern test)) =
      mu.real (F.event i) := by
  rw [Measure.real, incidencePatternLaw,
    Measure.map_apply F.measurable_incidencePattern
      MeasurableSet.of_discrete,
    preimage_truePatterns (F := F) i]
  rfl

abbrev PatternSample (n : Nat) :=
  Family8FiniteProbabilityCeilRoundingV1.CeilSample
    (F.incidencePatternLaw mu) n

def sampledPattern {n : Nat} (g : F.PatternSample mu n) : Pattern test :=
  Family8FiniteProbabilityCeilRoundingV1.ceilSampleValue
    (F.incidencePatternLaw mu) g

theorem sampledPattern_fiber_nonempty {n : Nat}
    (g : F.PatternSample mu n) :
    (F.incidencePattern ⁻¹'
        ({F.sampledPattern mu g} : Set (Pattern test))).Nonempty := by
  by_contra hnonempty
  have hfiber :
      F.incidencePattern ⁻¹'
          ({F.sampledPattern mu g} : Set (Pattern test)) =
        (∅ : Set Omega) :=
    Set.not_nonempty_iff_eq_empty.mp hnonempty
  have hmass :
      (F.incidencePatternLaw mu).real {F.sampledPattern mu g} = 0 := by
    rw [Measure.real, incidencePatternLaw,
      Measure.map_apply F.measurable_incidencePattern
        (measurableSet_singleton _), hfiber, measure_empty,
      ENNReal.toReal_zero]
  have hmultiplicity :
      Family8FiniteProbabilityCeilRoundingV1.ceilMultiplicity
          (F.incidencePatternLaw mu) n (F.sampledPattern mu g) = 0 := by
    simp [Family8FiniteProbabilityCeilRoundingV1.ceilMultiplicity, hmass]
  change Family8FiniteProbabilityCeilRoundingV1.ceilMultiplicity
      (F.incidencePatternLaw mu) n g.1 = 0 at hmultiplicity
  have hpositive :
      0 < Family8FiniteProbabilityCeilRoundingV1.ceilMultiplicity
          (F.incidencePatternLaw mu) n g.1 :=
    lt_of_le_of_lt (Nat.zero_le g.2.val) g.2.isLt
  exact (Nat.ne_of_gt hpositive) hmultiplicity

def sampleRepresentative {n : Nat} (g : F.PatternSample mu n) : Omega :=
  Classical.choose (F.sampledPattern_fiber_nonempty mu g)

theorem incidencePattern_sampleRepresentative {n : Nat}
    (g : F.PatternSample mu n) :
    F.incidencePattern (F.sampleRepresentative mu g) =
      F.sampledPattern mu g := by
  exact Set.mem_singleton_iff.mp
    (Classical.choose_spec (F.sampledPattern_fiber_nonempty mu g))

theorem sampleRepresentative_mem_event_iff {n : Nat}
    (g : F.PatternSample mu n) (i : test) :
    F.sampleRepresentative mu g ∈ F.event i ↔
      F.sampledPattern mu g ∈ truePatterns (test := test) i := by
  simp only [truePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hmem
    have hp :
        F.incidencePattern (F.sampleRepresentative mu g) i := by
      simpa [incidencePattern] using hmem
    rw [F.incidencePattern_sampleRepresentative mu g] at hp
    exact hp
  · intro hp
    have hmem :
        F.incidencePattern (F.sampleRepresentative mu g) i := by
      rw [F.incidencePattern_sampleRepresentative mu g]
      exact hp
    simpa [incidencePattern] using hmem

def sampleEventFinset (n : Nat) (i : test) :
    Finset (F.PatternSample mu n) :=
  @Finset.filter (F.PatternSample mu n)
    (fun g => F.sampleRepresentative mu g ∈ F.event i)
    (fun g => Classical.propDecidable
      (F.sampleRepresentative mu g ∈ F.event i))
    Finset.univ

theorem scale_le_card_patternSample (n : Nat) :
    (n : Real) <= Fintype.card (F.PatternSample mu n) :=
  Family8FiniteProbabilityCeilRoundingV1.scale_le_card_ceilSample
    (F.incidencePatternLaw mu) n

theorem card_sampleRepresentative_event_le
    (n : Nat) (i : test) :
    ((F.sampleEventFinset mu n i).card : Real) <=
      (n : Real) * mu.real (F.event i) +
        (truePatterns (test := test) i).card := by
  classical
  have hfilter :
      F.sampleEventFinset mu n i =
        Finset.univ.filter
          (fun g : F.PatternSample mu n =>
            F.sampledPattern mu g ∈ truePatterns (test := test) i) := by
    apply Finset.ext
    intro g
    simp only [sampleEventFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact F.sampleRepresentative_mem_event_iff mu g i
  rw [hfilter]
  have hround :=
    Family8FiniteProbabilityCeilRoundingV1.card_ceilSample_filter_le_scaled_measure_add_card
      (F.incidencePatternLaw mu) n (truePatterns (test := test) i)
  rw [F.incidencePatternLaw_real_truePatterns mu i] at hround
  exact hround

theorem card_sampleRepresentative_event_le_patternCard
    (n : Nat) (i : test) :
    ((F.sampleEventFinset mu n i).card : Real) <=
      (n : Real) * mu.real (F.event i) + Fintype.card (Pattern test) := by
  classical
  exact (F.card_sampleRepresentative_event_le mu n i).trans <| by
    gcongr
    exact_mod_cast
      Finset.card_le_univ (s := truePatterns (test := test) i)

#print axioms measurable_incidencePattern
#print axioms incidencePatternLaw_real_truePatterns
#print axioms sampledPattern_fiber_nonempty
#print axioms incidencePattern_sampleRepresentative
#print axioms sampleRepresentative_mem_event_iff
#print axioms scale_le_card_patternSample
#print axioms card_sampleRepresentative_event_le
#print axioms card_sampleRepresentative_event_le_patternCard

end MeasurableEventFamily

end
end Family8FiniteIncidencePatternSamplerV7
