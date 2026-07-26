import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Optics.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0147

/-!
# Refractive-index range for a liquid-detecting prism

The intended device is a right-isosceles prism. A source ray enters one leg
normally and strikes the hypotenuse at `45°`. When the hypotenuse is exposed
to air, total internal reflection directs the beam to a sensor. When water
covers that face, part of the beam is transmitted into the water and the
sensor signal decreases.

Refractive indices and displayed answer endpoints are dimensionless real
readouts. Ray angles are represented by Mathlib's physical angle type
`Real.Angle`.

`Physlib.Optics.Basic` is imported as the relevant formal-physics module, but
it is currently a placeholder. The critical-interface and sensor-response
laws are therefore stated below as explicit local interfaces.

The bitmap attached to the source record depicts an unrelated two-lens system.
Consequently the intended `45°` prism geometry is kept as an explicit model
hypothesis below rather than asserted as a readout of that bitmap.
-/

/-- The three prism faces met by, or relevant to, the detector beam. -/
inductive PrismFace where
  | sourceEntryFace
  | sensorExitFace
  | hypotenuse
  deriving DecidableEq, Repr

/-- Shape of the prism cross-section intended by the detector description. -/
inductive PrismCrossSection where
  | rightIsosceles
  deriving DecidableEq, Repr

/-- Whether the externally accessible hypotenuse is dry or covered by liquid. -/
inductive HypotenuseContact where
  | noLiquid
  | coveredByLiquid
  deriving DecidableEq, Repr

/-- The two qualitative light-sensor readouts described in the problem. -/
inductive SensorSignal where
  | large
  | decreased
  deriving DecidableEq, Repr

/-- Convert a real-valued degree readout into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-!
Combinatorial geometry of the intended detector diagram. The fields retain
the source-facing leg, the sensor-facing leg, and the reservoir-contact face
without assigning an answer interval to the prism index.
-/
structure PrismDetectorDiagram where
  crossSection : PrismCrossSection
  sourceEntryFace : PrismFace
  sensorExitFace : PrismFace
  reservoirContactFace : PrismFace

/-!
Optical observables of the detector for a hypothetical positive prism index.
The external refractive index depends on whether the hypotenuse is exposed to
air or covered by reservoir liquid. Optical outcomes and the sensor readout
remain primitive observations; governing laws relate them below.
-/
structure LiquidDetectorPrismSetup where
  diagram : PrismDetectorDiagram
  incidenceAngleToNormal : PrismFace → Real.Angle
  externalRefractiveIndex : HypotenuseContact → ℝ
  totallyInternallyReflected : ℝ → HypotenuseContact → Prop
  lightEscapesIntoExternalMedium : ℝ → HypotenuseContact → Prop
  sensorSignal : ℝ → HypotenuseContact → SensorSignal

/-!
The intended component layout: a right-isosceles prism, normal entry through
one leg, sensor exit through the other leg, and liquid contact at the
hypotenuse. This is a model assumption, not a readout of the mismatched bitmap.
-/
def MatchesIntendedDetectorLayout
    (setup : LiquidDetectorPrismSetup) : Prop :=
  setup.diagram.crossSection = .rightIsosceles ∧
    setup.diagram.sourceEntryFace = .sourceEntryFace ∧
    setup.diagram.sensorExitFace = .sensorExitFace ∧
    setup.diagram.reservoirContactFace = .hypotenuse

/-!
Normal source entry leaves the internal ray undeviated. In a right-isosceles
cross-section it then meets the hypotenuse at `45°` from the face normal.
-/
def HasIntendedRayGeometry (setup : LiquidDetectorPrismSetup) : Prop :=
  setup.incidenceAngleToNormal .sourceEntryFace = 0 ∧
    setup.incidenceAngleToNormal .hypotenuse = degrees 45

/-!
The dimensionless textbook environmental indices used by the recorded answer:
`n_air = 1.00` and `n_water = 1.33`. These are calibration assumptions, not
the requested prism-index bounds.
-/
def UsesStandardAirWaterIndices
    (setup : LiquidDetectorPrismSetup) : Prop :=
  setup.externalRefractiveIndex .noLiquid = 1 ∧
    setup.externalRefractiveIndex .coveredByLiquid = (133 / 100 : ℝ)

/-- Positivity, optical ordering, and the acute physical incidence branch. -/
def HasPhysicalParameters (setup : LiquidDetectorPrismSetup) : Prop :=
  (∀ contact, 0 < setup.externalRefractiveIndex contact) ∧
    setup.externalRefractiveIndex .noLiquid <
      setup.externalRefractiveIndex .coveredByLiquid ∧
    0 < (setup.incidenceAngleToNormal .hypotenuse).toReal ∧
    (setup.incidenceAngleToNormal .hypotenuse).toReal < Real.pi / 2

/-!
Critical-angle optics at the prism hypotenuse, uniformly for every candidate
positive prism index.

Strict total internal reflection occurs when the external index is below
`n_prism sin θ`. Light genuinely enters the external medium when that
quantity is strictly below the external index. Equality is the grazing
critical case and is excluded from both operating states. Neither criterion
contains the requested numerical interval.
-/
structure SatisfiesPrismInterfaceOptics
    (setup : LiquidDetectorPrismSetup) : Prop where
  totalInternalReflectionCriterion :
    ∀ prismIndex : ℝ, 0 < prismIndex → ∀ contact : HypotenuseContact,
      (setup.totallyInternallyReflected prismIndex contact ↔
        setup.externalRefractiveIndex contact <
          prismIndex *
            Real.Angle.sin (setup.incidenceAngleToNormal .hypotenuse))
  transmissionCriterion :
    ∀ prismIndex : ℝ, 0 < prismIndex → ∀ contact : HypotenuseContact,
      (setup.lightEscapesIntoExternalMedium prismIndex contact ↔
        prismIndex *
            Real.Angle.sin (setup.incidenceAngleToNormal .hypotenuse) <
          setup.externalRefractiveIndex contact)

/-!
Response law of the idealized sensor. Reflected light gives the large signal;
transmission into the exterior decreases it. This law does not assert which
contact state produces either optical outcome.
-/
structure SatisfiesSensorResponse
    (setup : LiquidDetectorPrismSetup) : Prop where
  signalFromTotalInternalReflection :
    ∀ prismIndex contact,
      setup.totallyInternallyReflected prismIndex contact →
        setup.sensorSignal prismIndex contact = .large
  signalFromEscapingLight :
    ∀ prismIndex contact,
      setup.lightEscapesIntoExternalMedium prismIndex contact →
        setup.sensorSignal prismIndex contact = .decreased

/-!
A candidate prism index is allowable precisely when it produces the two
required physical operating modes: TIR while dry and transmission while wet.
This definition is behavioral; it does not unfold to the requested bounds.
-/
def IsAllowablePrismIndex
    (setup : LiquidDetectorPrismSetup) (prismIndex : ℝ) : Prop :=
  0 < prismIndex ∧
    setup.totallyInternallyReflected prismIndex .noLiquid ∧
    setup.lightEscapesIntoExternalMedium prismIndex .coveredByLiquid

/-- All dimensionless prism indices for which the detector operates correctly. -/
def allowablePrismIndices (setup : LiquidDetectorPrismSetup) : Set ℝ :=
  {prismIndex | IsAllowablePrismIndex setup prismIndex}

/-- Labels of the four refractive-index ranges displayed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Printed lower endpoint of each dimensionless answer interval. -/
def displayedLowerIndexBound : AnswerChoice → ℝ
  | .A => 141 / 100
  | .B => 131 / 100
  | .C => 141 / 100
  | .D => 151 / 100

/-- Printed upper endpoint of each dimensionless answer interval. -/
def displayedUpperIndexBound : AnswerChoice → ℝ
  | .A => 198 / 100
  | .B => 188 / 100
  | .C => 188 / 100
  | .D => 178 / 100

/-- The open prism-index interval printed beside an answer label. -/
def displayedPrismIndexInterval (choice : AnswerChoice) : Set ℝ :=
  Set.Ioo (displayedLowerIndexBound choice) (displayedUpperIndexBound choice)

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed two-decimal interval matches exact physical endpoints when each
endpoint is within half a hundredth. This expresses numerical rounding and
does not make any particular choice correct by definition.
-/
def MatchesRoundedAllowableRange
    (exactLower exactUpper : ℝ) (choice : AnswerChoice) : Prop :=
  |exactLower - displayedLowerIndexBound choice| ≤ (1 / 200 : ℝ) ∧
    |exactUpper - displayedUpperIndexBound choice| ≤ (1 / 200 : ℝ)

/-!
The intended `45°` incidence geometry gives `sin θ = √2 / 2`. This is a
derived trigonometric relation.
-/
lemma hypotenuseIncidenceSine_eq_sqrtTwoOverTwo
    (setup : LiquidDetectorPrismSetup)
    (h_geometry : HasIntendedRayGeometry setup) :
    Real.Angle.sin (setup.incidenceAngleToNormal .hypotenuse) =
      Real.sqrt 2 / 2 := by
  rw [h_geometry.2, degrees, Real.Angle.sin_coe]
  have h : (45 : ℝ) * Real.pi / 180 = Real.pi / 4 := by
    ring
  rw [h, Real.sin_pi_div_four]

/-!
The critical-angle and transmission laws characterize the exact, unrounded
operating range. Air-side TIR gives `√2 < n`, while transmission into water
gives `n < 1.33 √2`.
-/
lemma allowablePrismIndices_eq_exactInterval
    (setup : LiquidDetectorPrismSetup)
    (h_geometry : HasIntendedRayGeometry setup)
    (h_indices : UsesStandardAirWaterIndices setup)
    (h_optics : SatisfiesPrismInterfaceOptics setup) :
    allowablePrismIndices setup =
      Set.Ioo (Real.sqrt 2) ((133 / 100 : ℝ) * Real.sqrt 2) := by
  ext prismIndex
  constructor
  · intro h
    change IsAllowablePrismIndex setup prismIndex at h
    rcases h with ⟨h_prism_pos, h_tir, h_transmit⟩
    have h_sine :=
      hypotenuseIncidenceSine_eq_sqrtTwoOverTwo setup h_geometry
    have h_tir_ineq :=
      (h_optics.totalInternalReflectionCriterion
        prismIndex h_prism_pos .noLiquid).mp h_tir
    have h_transmit_ineq :=
      (h_optics.transmissionCriterion
        prismIndex h_prism_pos .coveredByLiquid).mp h_transmit
    rw [h_indices.1, h_sine] at h_tir_ineq
    rw [h_indices.2, h_sine] at h_transmit_ineq
    change Real.sqrt 2 < prismIndex ∧
      prismIndex < (133 / 100 : ℝ) * Real.sqrt 2
    have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h_sqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    constructor <;> nlinarith
  · intro h
    change Real.sqrt 2 < prismIndex ∧
      prismIndex < (133 / 100 : ℝ) * Real.sqrt 2 at h
    rcases h with ⟨h_lower, h_upper⟩
    have h_sine :=
      hypotenuseIncidenceSine_eq_sqrtTwoOverTwo setup h_geometry
    have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have h_prism_pos : 0 < prismIndex := lt_trans h_sqrt_pos h_lower
    have h_sqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    change IsAllowablePrismIndex setup prismIndex
    refine ⟨h_prism_pos, ?_, ?_⟩
    · apply (h_optics.totalInternalReflectionCriterion
        prismIndex h_prism_pos .noLiquid).2
      rw [h_indices.1, h_sine]
      nlinarith
    · apply (h_optics.transmissionCriterion
        prismIndex h_prism_pos .coveredByLiquid).2
      rw [h_indices.2, h_sine]
      nlinarith

/-!
For any allowable prism index, the sensor has a large signal exactly in the
absence of liquid. Thus the qualitative inference stated in the scenario is
derived from the operating modes and sensor law, not assumed.
-/
lemma largeSensorSignal_iff_noLiquid
    (setup : LiquidDetectorPrismSetup)
    (h_sensor : SatisfiesSensorResponse setup)
    (prismIndex : ℝ)
    (h_allowable : IsAllowablePrismIndex setup prismIndex)
    (contact : HypotenuseContact) :
    setup.sensorSignal prismIndex contact = .large ↔
      contact = .noLiquid := by
  constructor
  · intro h_large
    cases contact with
    | noLiquid => rfl
    | coveredByLiquid =>
        have h_decreased :=
          h_sensor.signalFromEscapingLight prismIndex .coveredByLiquid
            h_allowable.2.2
        rw [h_decreased] at h_large
        contradiction
  · intro h_contact
    subst contact
    exact h_sensor.signalFromTotalInternalReflection prismIndex .noLiquid
      h_allowable.2.1

/-!
The exact allowable range for the prism material is

`√2 < n < 1.33 √2`.

Its endpoints round to `1.41` and `1.88`, so it matches displayed choice C.
Every index in the exact interval also gives the detector interpretation: a
large sensor signal occurs exactly when no liquid covers the hypotenuse.

This formalizes `thm:physics:phyx_mini_0147:target`. No premise contains the
exact interval, its rounded endpoints, or the selected answer choice.
-/
theorem problem_phyx_mini_0147
    (setup : LiquidDetectorPrismSetup)
    (h_layout : MatchesIntendedDetectorLayout setup)
    (h_geometry : HasIntendedRayGeometry setup)
    (h_indices : UsesStandardAirWaterIndices setup)
    (h_physical : HasPhysicalParameters setup)
    (h_optics : SatisfiesPrismInterfaceOptics setup)
    (h_sensor : SatisfiesSensorResponse setup) :
    allowablePrismIndices setup =
        Set.Ioo (Real.sqrt 2) ((133 / 100 : ℝ) * Real.sqrt 2) ∧
      MatchesRoundedAllowableRange
        (Real.sqrt 2) ((133 / 100 : ℝ) * Real.sqrt 2)
        recordedDatasetAnswer ∧
      ∀ prismIndex : ℝ, prismIndex ∈ allowablePrismIndices setup →
        ∀ contact : HypotenuseContact,
          setup.sensorSignal prismIndex contact = .large ↔
            contact = .noLiquid := by
  constructor
  · exact
      allowablePrismIndices_eq_exactInterval setup h_geometry h_indices h_optics
  constructor
  · change |Real.sqrt 2 - 141 / 100| ≤ (1 / 200 : ℝ) ∧
      |(133 / 100 : ℝ) * Real.sqrt 2 - 188 / 100| ≤ (1 / 200 : ℝ)
    have h_sqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    constructor <;> rw [abs_le] <;> constructor <;>
      nlinarith [Real.sqrt_nonneg 2]
  · intro prismIndex h_prism contact
    exact
      largeSensorSignal_iff_noLiquid setup h_sensor prismIndex h_prism contact

end PhyXMiniProblems.ProblemPhyXMini0147
