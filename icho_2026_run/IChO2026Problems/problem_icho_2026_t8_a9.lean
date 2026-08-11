import IChO2026Chem
import CRNT.Basic.Reaction
import Mathlib

/-!
# IChO 2026 T8-A9: reductive quenching of a photosensitiser

This file models the two excited photosensitiser states separately from the
scalar kinetic measurements.  First-order rate constants are numerical values
in `s⁻¹`, bimolecular quenching constants in `M⁻¹ s⁻¹`, lifetimes in `s`, and
the reductant concentration in `M`.  Consequently, the products `k τ [Red]`
used below are dimensionless, as required for quenching fractions.

The printed condition `k_F >> k_ISC` is qualitative: the problem gives no
numerical comparison factor or error tolerance.  It is therefore retained as
an explicit dominance hypothesis, while the lifetime formula using
`k_F + k_IC` records the stated kinetic approximation.
-/

namespace IChO2026Problems.T8A9

noncomputable section

/-- The photosensitiser states and reductant species distinguished in T8-A9. -/
private inductive PhotochemicalSpecies where
  | photosensitiserGroundState
  | photosensitiserSingletExcited
  | photosensitiserTripletExcited
  | photosensitiserRadicalAnion
  | reductant
  | reductantRadicalCation
  deriving DecidableEq, Fintype, Repr

/-- Numerical value of a first-order photophysical rate constant, in `s⁻¹`. -/
private abbrev FirstOrderRateConstant := ℝ

/-- Numerical value of a bimolecular quenching rate constant, in `M⁻¹ s⁻¹`. -/
private abbrev BimolecularRateConstant := ℝ

/-- Emission lifetime in the absence of a quencher, in `s`. -/
private abbrev EmissionLifetime := ℝ

/-- Reductant concentration, in `M`. -/
private abbrev MolarConcentration := ℝ

/-- A dimensionless fraction of excited molecules that are quenched. -/
private abbrev QuenchingFraction := ℝ

/-- A quenching fraction expressed on the percentage scale. -/
private abbrev QuenchingPercent := ℝ

/-- `PS(S₁) + Red → PS•⁻ + Red•⁺`, the reductive singlet-state quenching
reaction printed in the problem. -/
private def singletReductiveQuenching : CRNT.Reaction PhotochemicalSpecies where
  source
    | .photosensitiserGroundState => 0
    | .photosensitiserSingletExcited => 1
    | .photosensitiserTripletExcited => 0
    | .photosensitiserRadicalAnion => 0
    | .reductant => 1
    | .reductantRadicalCation => 0
  target
    | .photosensitiserGroundState => 0
    | .photosensitiserSingletExcited => 0
    | .photosensitiserTripletExcited => 0
    | .photosensitiserRadicalAnion => 1
    | .reductant => 0
    | .reductantRadicalCation => 1

/-- `PS(T₁) + Red → PS•⁻ + Red•⁺`, the reductive triplet-state quenching
reaction printed in the problem. -/
private def tripletReductiveQuenching : CRNT.Reaction PhotochemicalSpecies where
  source
    | .photosensitiserGroundState => 0
    | .photosensitiserSingletExcited => 0
    | .photosensitiserTripletExcited => 1
    | .photosensitiserRadicalAnion => 0
    | .reductant => 1
    | .reductantRadicalCation => 0
  target
    | .photosensitiserGroundState => 0
    | .photosensitiserSingletExcited => 0
    | .photosensitiserTripletExcited => 0
    | .photosensitiserRadicalAnion => 1
    | .reductant => 0
    | .reductantRadicalCation => 1

/-- The kinetic readouts and decay pathways represented in the Jablonski
diagram.  The six first-order fields correspond respectively to `k_F`,
`k_IC`, `k_ISC`, `k_P`, `k_N`, and `k_RISC`; the two bimolecular fields are
the displayed `k_S` and `k_T`. -/
private structure PhotosensitiserQuenchingExperiment where
  singletQuenchingReaction : CRNT.Reaction PhotochemicalSpecies
  tripletQuenchingReaction : CRNT.Reaction PhotochemicalSpecies
  fluorescenceRate : FirstOrderRateConstant
  internalConversionRate : FirstOrderRateConstant
  intersystemCrossingRate : FirstOrderRateConstant
  phosphorescenceRate : FirstOrderRateConstant
  tripletNonradiativeRate : FirstOrderRateConstant
  reverseIntersystemCrossingRate : FirstOrderRateConstant
  singletQuenchingRate : BimolecularRateConstant
  tripletQuenchingRate : BimolecularRateConstant
  singletLifetimeWithoutQuencher : EmissionLifetime
  tripletLifetimeWithoutQuencher : EmissionLifetime
  reductantConcentration : MolarConcentration
  fluorescenceRate_positive : 0 < fluorescenceRate
  internalConversionRate_nonnegative : 0 ≤ internalConversionRate
  intersystemCrossingRate_nonnegative : 0 ≤ intersystemCrossingRate
  phosphorescenceRate_positive : 0 < phosphorescenceRate
  tripletNonradiativeRate_nonnegative : 0 ≤ tripletNonradiativeRate
  reverseIntersystemCrossingRate_nonnegative : 0 ≤ reverseIntersystemCrossingRate
  singletQuenchingRate_positive : 0 < singletQuenchingRate
  tripletQuenchingRate_positive : 0 < tripletQuenchingRate
  singletLifetimeWithoutQuencher_positive : 0 < singletLifetimeWithoutQuencher
  tripletLifetimeWithoutQuencher_positive : 0 < tripletLifetimeWithoutQuencher
  reductantConcentration_nonnegative : 0 ≤ reductantConcentration

/-- The full unquenched first-order decay rate of `S₁` shown by the
Jablonski diagram. -/
private def singletDecayRateBeforeQuenching (experiment : PhotosensitiserQuenchingExperiment) :
    FirstOrderRateConstant :=
  experiment.fluorescenceRate + experiment.internalConversionRate +
    experiment.intersystemCrossingRate

/-- The approximate unquenched `S₁` decay rate used in the official solution
after dropping the small `k_ISC` contribution. -/
private def singletApproximateDecayRate (experiment : PhotosensitiserQuenchingExperiment) :
    FirstOrderRateConstant :=
  experiment.fluorescenceRate + experiment.internalConversionRate

/-- The unquenched first-order decay rate of `T₁` shown by the Jablonski
diagram. -/
private def tripletDecayRateBeforeQuenching (experiment : PhotosensitiserQuenchingExperiment) :
    FirstOrderRateConstant :=
  experiment.phosphorescenceRate + experiment.tripletNonradiativeRate +
    experiment.reverseIntersystemCrossingRate

/-- A scalar version of the printed qualitative relation `larger >> smaller`.
The source specifies no numerical threshold, so the comparison factor remains
an explicit parameter rather than an invented experimental value. -/
private def DominatesByFactor (larger smaller factor : ℝ) : Prop :=
  1 < factor ∧ 0 ≤ smaller ∧ factor * smaller ≤ larger

/-- The source's kinetic modelling assumptions.  The `S₁` lifetime equation
is explicitly an approximation based on the supplied qualitative dominance
condition; no unreported approximation error is postulated. -/
private structure UsesT8A9LifetimeModel
    (experiment : PhotosensitiserQuenchingExperiment) : Prop where
  fluorescence_dominates_intersystem_crossing :
    ∃ factor : ℝ,
      DominatesByFactor experiment.fluorescenceRate
        experiment.intersystemCrossingRate factor
  singlet_lifetime_approximation :
    ∀ factor : ℝ,
      DominatesByFactor experiment.fluorescenceRate
          experiment.intersystemCrossingRate factor →
        experiment.singletLifetimeWithoutQuencher =
          1 / singletApproximateDecayRate experiment
  triplet_lifetime_law :
    experiment.tripletLifetimeWithoutQuencher =
      1 / tripletDecayRateBeforeQuenching experiment

/-- Dimensionless stoichiometric factor converting a reaction-event rate to
formation of `PS•⁻`.  It is one exactly for either printed T8-A9 quenching
reaction: one excited photosensitiser and one reductant are consumed, and one
radical anion and one radical cation are formed. -/
private def reductiveQuenchingEventFactor
    (reaction : CRNT.Reaction PhotochemicalSpecies) : ℝ :=
  ((reaction.source .photosensitiserSingletExcited +
      reaction.source .photosensitiserTripletExcited) *
    reaction.source .reductant *
      reaction.target .photosensitiserRadicalAnion *
        reaction.target .reductantRadicalCation : ℕ)

/-- The pseudo-first-order formation rate for the reductively quenched
photoproduct.  The reaction map remains an input: changing the reaction's
stoichiometry can change this physical rate even if its scalar rate constant
is held fixed. -/
private def reductivePseudoFirstOrderRate
    (reaction : CRNT.Reaction PhotochemicalSpecies)
    (bimolecularRate : BimolecularRateConstant)
    (concentration : MolarConcentration) : FirstOrderRateConstant :=
  reductiveQuenchingEventFactor reaction * bimolecularRate * concentration

/-- The rate-law fraction for two competing first-order processes: intrinsic
decay with rate `intrinsicDecayRate` and reductive quenching through the
specified reaction channel. -/
private def quenchingFractionByCompetition
    (reaction : CRNT.Reaction PhotochemicalSpecies)
    (intrinsicDecayRate : FirstOrderRateConstant)
    (bimolecularRate : BimolecularRateConstant)
    (concentration : MolarConcentration) : QuenchingFraction :=
  reductivePseudoFirstOrderRate reaction bimolecularRate concentration /
    (intrinsicDecayRate +
      reductivePseudoFirstOrderRate reaction bimolecularRate concentration)

/-- The equivalent lifetime form `k τ [Red] / (1 + k τ [Red])` used for the
calculation once the unquenched lifetime is known. -/
private def quenchingFractionFromLifetime
    (bimolecularRate : BimolecularRateConstant)
    (lifetime : EmissionLifetime)
    (concentration : MolarConcentration) : QuenchingFraction :=
  (bimolecularRate * lifetime * concentration) /
    (1 + bimolecularRate * lifetime * concentration)

/-- Percentage of a quenching fraction. -/
private def quenchingPercentage (fraction : QuenchingFraction) : QuenchingPercent :=
  100 * fraction

/-- The singlet-state quenching fraction, retaining the `k_F >> k_ISC`
lifetime approximation used in the official calculation. -/
private def singletQuenchingFraction (experiment : PhotosensitiserQuenchingExperiment) :
    QuenchingFraction :=
  quenchingFractionByCompetition experiment.singletQuenchingReaction
    (singletApproximateDecayRate experiment)
    experiment.singletQuenchingRate experiment.reductantConcentration

/-- The triplet-state quenching fraction. -/
private def tripletQuenchingFraction (experiment : PhotosensitiserQuenchingExperiment) :
    QuenchingFraction :=
  quenchingFractionByCompetition experiment.tripletQuenchingReaction
    (tripletDecayRateBeforeQuenching experiment)
    experiment.tripletQuenchingRate experiment.reductantConcentration

/-- The two reactions are precisely the reductive quenching reactions stated
in T8-A9. -/
private def HasT8A9QuenchingMechanism (experiment : PhotosensitiserQuenchingExperiment) : Prop :=
  experiment.singletQuenchingReaction = singletReductiveQuenching ∧
    experiment.tripletQuenchingReaction = tripletReductiveQuenching

/-- The numerical kinetic observations supplied in T8-A9.  The requested
quenching fractions and percentages are intentionally not fields here. -/
private def MatchesT8A9SourceData (experiment : PhotosensitiserQuenchingExperiment) : Prop :=
  experiment.singletQuenchingRate = 2.7 * 10 ^ 9 ∧
    experiment.tripletQuenchingRate = 1.5 * 10 ^ 8 ∧
      experiment.singletLifetimeWithoutQuencher = 2.9 / 10 ^ 9 ∧
        experiment.tripletLifetimeWithoutQuencher = 84 / 10 ^ 6 ∧
          experiment.reductantConcentration = 1 / 10

/-- A reported percentage rounded to the nearest whole percentage point. -/
private def RoundsToWholePercent (value reported : QuenchingPercent) : Prop :=
  |value - reported| < (1 : ℝ) / 2

/-- A reported percentage rounded to one decimal place. -/
private def RoundsToOneDecimalPercent (value reported : QuenchingPercent) : Prop :=
  |value - reported| < (1 : ℝ) / 20

/-- The two lifetime forms of the quenching fractions (equations 8.10.3 and
8.10.4 in the official solution).  The nonzero decay-rate side conditions are
made explicit because division by a rate occurs in the lifetime bridge. -/
private theorem quenching_fractions_from_lifetimes
    (experiment : PhotosensitiserQuenchingExperiment)
    (hmechanism : HasT8A9QuenchingMechanism experiment)
    (hmodel : UsesT8A9LifetimeModel experiment)
    (hsinglet_decay_ne_zero : singletApproximateDecayRate experiment ≠ 0)
    (htriplet_decay_ne_zero : tripletDecayRateBeforeQuenching experiment ≠ 0) :
    singletQuenchingFraction experiment =
      quenchingFractionFromLifetime experiment.singletQuenchingRate
        experiment.singletLifetimeWithoutQuencher experiment.reductantConcentration ∧
      tripletQuenchingFraction experiment =
        quenchingFractionFromLifetime experiment.tripletQuenchingRate
          experiment.tripletLifetimeWithoutQuencher experiment.reductantConcentration := by
  constructor
  · rw [singletQuenchingFraction, quenchingFractionByCompetition,
    reductivePseudoFirstOrderRate, reductiveQuenchingEventFactor,
    hmechanism.1, quenchingFractionFromLifetime]
    norm_num [singletReductiveQuenching]
    rcases hmodel.fluorescence_dominates_intersystem_crossing with
      ⟨factor, hdominance⟩
    rw [hmodel.singlet_lifetime_approximation factor hdominance]
    have hdecay_pos : 0 < singletApproximateDecayRate experiment := by
      dsimp [singletApproximateDecayRate]
      linarith [experiment.fluorescenceRate_positive,
        experiment.internalConversionRate_nonnegative]
    have hcompetition_den_pos :
        0 < singletApproximateDecayRate experiment +
          experiment.singletQuenchingRate * experiment.reductantConcentration := by
      have hquenching_nonnegative :
          0 ≤ experiment.singletQuenchingRate * experiment.reductantConcentration :=
        mul_nonneg (le_of_lt experiment.singletQuenchingRate_positive)
          experiment.reductantConcentration_nonnegative
      linarith
    have hlifetime_den_pos :
        0 < 1 + experiment.singletQuenchingRate *
          (1 / singletApproximateDecayRate experiment) * experiment.reductantConcentration := by
      have hreciprocal_pos : 0 < 1 / singletApproximateDecayRate experiment :=
        one_div_pos.mpr hdecay_pos
      have hquenching_nonnegative :
          0 ≤ experiment.singletQuenchingRate *
            (1 / singletApproximateDecayRate experiment) * experiment.reductantConcentration := by
        exact mul_nonneg
          (mul_nonneg (le_of_lt experiment.singletQuenchingRate_positive)
            (le_of_lt hreciprocal_pos))
          experiment.reductantConcentration_nonnegative
      linarith
    field_simp [hsinglet_decay_ne_zero, hcompetition_den_pos.ne', hlifetime_den_pos.ne']
  · rw [tripletQuenchingFraction, quenchingFractionByCompetition,
    reductivePseudoFirstOrderRate, reductiveQuenchingEventFactor,
    hmechanism.2, quenchingFractionFromLifetime,
    hmodel.triplet_lifetime_law]
    norm_num [tripletReductiveQuenching]
    have hdecay_pos : 0 < tripletDecayRateBeforeQuenching experiment := by
      dsimp [tripletDecayRateBeforeQuenching]
      linarith [experiment.phosphorescenceRate_positive,
        experiment.tripletNonradiativeRate_nonnegative,
        experiment.reverseIntersystemCrossingRate_nonnegative]
    have hcompetition_den_pos :
        0 < tripletDecayRateBeforeQuenching experiment +
          experiment.tripletQuenchingRate * experiment.reductantConcentration := by
      have hquenching_nonnegative :
          0 ≤ experiment.tripletQuenchingRate * experiment.reductantConcentration :=
        mul_nonneg (le_of_lt experiment.tripletQuenchingRate_positive)
          experiment.reductantConcentration_nonnegative
      linarith
    have hlifetime_den_pos :
        0 < 1 + experiment.tripletQuenchingRate *
          (1 / tripletDecayRateBeforeQuenching experiment) *
            experiment.reductantConcentration := by
      have hreciprocal_pos : 0 < 1 / tripletDecayRateBeforeQuenching experiment :=
        one_div_pos.mpr hdecay_pos
      have hquenching_nonnegative :
          0 ≤ experiment.tripletQuenchingRate *
            (1 / tripletDecayRateBeforeQuenching experiment) *
              experiment.reductantConcentration := by
        exact mul_nonneg
          (mul_nonneg (le_of_lt experiment.tripletQuenchingRate_positive)
            (le_of_lt hreciprocal_pos))
          experiment.reductantConcentration_nonnegative
      linarith
    field_simp [htriplet_decay_ne_zero, hcompetition_den_pos.ne', hlifetime_den_pos.ne']

/-- T8-A9.  With the stated reductant concentration, the singlet state has a
quenching percentage that rounds to `44%`, whereas the triplet state has a
quenching percentage that rounds to `99.9%`.  The calculation uses the
explicit source kinetic model and does not store either requested answer in
the experimental data. -/
theorem calculate_singlet_and_triplet_quenching_percentages
    (experiment : PhotosensitiserQuenchingExperiment)
    (hmechanism : HasT8A9QuenchingMechanism experiment)
    (hmodel : UsesT8A9LifetimeModel experiment)
    (hsource : MatchesT8A9SourceData experiment) :
    singletQuenchingFraction experiment =
      quenchingFractionFromLifetime experiment.singletQuenchingRate
        experiment.singletLifetimeWithoutQuencher experiment.reductantConcentration ∧
      tripletQuenchingFraction experiment =
        quenchingFractionFromLifetime experiment.tripletQuenchingRate
          experiment.tripletLifetimeWithoutQuencher experiment.reductantConcentration ∧
      RoundsToWholePercent (quenchingPercentage (singletQuenchingFraction experiment)) 44 ∧
        RoundsToOneDecimalPercent
          (quenchingPercentage (tripletQuenchingFraction experiment)) 99.9 := by
  rcases hsource with ⟨hsinglet_rate, htriplet_rate, hsinglet_lifetime,
    htriplet_lifetime, hconcentration⟩
  have hsinglet_decay_ne_zero : singletApproximateDecayRate experiment ≠ 0 := by
    have hdecay_pos : 0 < singletApproximateDecayRate experiment := by
      dsimp [singletApproximateDecayRate]
      linarith [experiment.fluorescenceRate_positive,
        experiment.internalConversionRate_nonnegative]
    exact ne_of_gt hdecay_pos
  have htriplet_decay_ne_zero : tripletDecayRateBeforeQuenching experiment ≠ 0 := by
    have hdecay_pos : 0 < tripletDecayRateBeforeQuenching experiment := by
      dsimp [tripletDecayRateBeforeQuenching]
      linarith [experiment.phosphorescenceRate_positive,
        experiment.tripletNonradiativeRate_nonnegative,
        experiment.reverseIntersystemCrossingRate_nonnegative]
    exact ne_of_gt hdecay_pos
  have hfractions := quenching_fractions_from_lifetimes experiment hmechanism hmodel
    hsinglet_decay_ne_zero htriplet_decay_ne_zero
  refine ⟨hfractions.1, hfractions.2, ?_, ?_⟩
  · rw [hfractions.1]
    unfold RoundsToWholePercent quenchingPercentage quenchingFractionFromLifetime
    rw [hsinglet_rate, hsinglet_lifetime, hconcentration]
    norm_num [abs_of_nonpos]
  · rw [hfractions.2]
    unfold RoundsToOneDecimalPercent quenchingPercentage quenchingFractionFromLifetime
    rw [htriplet_rate, htriplet_lifetime, hconcentration]
    norm_num [abs_of_nonneg]

end

end IChO2026Problems.T8A9
