import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0298

open Dimension

/-!
# Fourth harmonic of a string tensioned by a hanging mass

The primary figure shows a sinusoidal oscillator attached to the string at
`P`.  The string runs horizontally from `P` to the support at `Q`, then turns
vertically downward to a block labelled `m`.  Both `P` and `Q` are nodes of
the vibrating segment, whose length is labelled `L`.

Mass, length, frequency, acceleration, tension, linear mass density, and wave
speed below are unit-independent Physlib quantities.  Real numbers occur only
as explicitly named coherent-SI readouts and displayed answer values.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative ordinary frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative string-tension magnitude, carrying force dimension. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length of string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A unit-independent, nonnegative propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Metre readout of the separation between `P` and `Q`. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- Hertz readout of the oscillator frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantityReadout UnitChoices.SI frequency

/-- Metres-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- Newton readout of a string tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  quantityReadout UnitChoices.SI tension

/-- Kilograms-per-metre readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Metres-per-second readout of a transverse wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-! ## Labels and topology from the primary figure -/

/-- The two labelled endpoints of the horizontal vibrating segment. -/
inductive FigurePoint where
  | P
  | Q
  deriving DecidableEq, Repr

/-- Individually identifiable objects and portions of string in the figure. -/
inductive FigureComponent where
  | oscillator
  | pointP
  | horizontalStringPQ
  | pointQ
  | supportAtQ
  | verticalString
  | hangingMassM
  deriving DecidableEq, Repr

/-- The two string portions separated by the support at `Q`. -/
inductive StringSegment where
  | vibratingPQ
  | hangingBelowQ
  deriving DecidableEq, Repr

/-- The complete route of the single string drawn in the primary figure. -/
inductive StringRoute where
  | oscillatorAtPToSupportAtQThenDownToMass
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative data for the pictured
apparatus.  In particular, `hangingMass` is not assigned the requested
numerical value here.
-/
structure OscillatorStringSetup where
  figureShows : FigureComponent → Prop
  oscillatorAttachment : FigurePoint
  supportLocation : FigurePoint
  stringRoute : StringRoute
  separationPQ : LengthQuantity
  stringLinearMassDensity : LinearMassDensityQuantity
  oscillatorFrequency : FrequencyQuantity
  hangingMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  segmentTension : StringSegment → TensionQuantity
  transverseWaveSpeed : SpeedQuantity
  oscillatorAmplitudeIsSmall : Prop
  isNodeAt : FigurePoint → Prop
  stringIsTautBetweenPAndQ : Prop
  supportIsFrictionless : Prop
  stringIsMassless : Prop
  hangingMassIsStatic : Prop
  oscillatorExcitesHarmonic : ℕ → Prop

/-!
The numerical data and categorical facts stated in the problem or visible in
the primary figure.  The density readout `1 / 625 kg/m` is the SI conversion
of `1.6 g/m`.  The requested mass and all four answer values are absent.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : OscillatorStringSetup) : Prop where
  showsEveryLabelledComponent : ∀ component, setup.figureShows component
  oscillatorAttachedAtP : setup.oscillatorAttachment = .P
  supportLocatedAtQ : setup.supportLocation = .Q
  routeReadout :
    setup.stringRoute = .oscillatorAtPToSupportAtQThenDownToMass
  separationMeters : lengthInMeters setup.separationPQ = 6 / 5
  linearDensityKilogramsPerMeter :
    linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity =
      1 / 625
  oscillatorFrequencyHertz :
    frequencyInHertz setup.oscillatorFrequency = 120
  smallOscillatorAmplitude : setup.oscillatorAmplitudeIsSmall
  pointPIsNode : setup.isNodeAt .P
  pointQIsNode : setup.isNodeAt .Q
  stringTaut : setup.stringIsTautBetweenPAndQ
  requestedModeIsFourthHarmonic : setup.oscillatorExcitesHarmonic 4

/-- The conventional near-Earth gravitational acceleration used by the choices. -/
structure UsesStandardEarthGravity
    (setup : OscillatorStringSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-- Positivity and nondegeneracy conditions for the taut-string model. -/
structure HasPositivePhysicalParameters
    (setup : OscillatorStringSetup) : Prop where
  separationPositive : 0 < lengthInMeters setup.separationPQ
  densityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity
  frequencyPositive : 0 < frequencyInHertz setup.oscillatorFrequency
  massPositive : 0 < massInKilograms setup.hangingMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  segmentTensionsPositive :
    ∀ segment, 0 < tensionInNewtons (setup.segmentTension segment)
  waveSpeedPositive : 0 < speedInMetersPerSecond setup.transverseWaveSpeed

/-! ## Governing ideal-support, string-wave, and harmonic laws -/

/-!
The standard textbook idealizations used in the calculation:

* a massless string over a frictionless support transmits the same tension;
* static balance makes the vertical tension equal to the hanging weight;
* a taut string obeys `v = sqrt (T / μ)`;
* a length-`L` segment with nodes at both ends has
  `fₙ = n v / (2 L)` in harmonic `n`.

These laws are stated generically and contain neither the requested mass nor
the recorded answer `0.846 kg`.
-/
structure SatisfiesIdealSupportStringAndHarmonicLaws
    (setup : OscillatorStringSetup) : Prop where
  supportFrictionless : setup.supportIsFrictionless
  stringMassless : setup.stringIsMassless
  hangingMassStatic : setup.hangingMassIsStatic
  supportTransmitsTension :
    setup.supportIsFrictionless →
      setup.stringIsMassless →
        tensionInNewtons (setup.segmentTension .vibratingPQ) =
          tensionInNewtons (setup.segmentTension .hangingBelowQ)
  hangingMassStaticBalance :
    setup.hangingMassIsStatic →
      tensionInNewtons (setup.segmentTension .hangingBelowQ) =
        massInKilograms setup.hangingMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  transverseWaveSpeedLaw :
    setup.stringIsTautBetweenPAndQ →
      speedInMetersPerSecond setup.transverseWaveSpeed =
        Real.sqrt
          (tensionInNewtons (setup.segmentTension .vibratingPQ) /
            linearMassDensityInKilogramsPerMeter
              setup.stringLinearMassDensity)
  fixedEndpointHarmonicLaw :
    ∀ harmonic : ℕ,
      0 < harmonic →
        setup.isNodeAt .P →
          setup.isNodeAt .Q →
            setup.oscillatorExcitesHarmonic harmonic →
              frequencyInHertz setup.oscillatorFrequency =
                (harmonic : ℝ) *
                    speedInMetersPerSecond setup.transverseWaveSpeed /
                  (2 * lengthInMeters setup.separationPQ)

/-! ## Derived exact values and displayed answer -/

/-!
The fourth-harmonic relation with `L = 1.20 m` and `f = 120 Hz` gives the
unrounded transverse wave speed `v = 72 m/s`.
-/
lemma fourthHarmonicWaveSpeed_exact
    (setup : OscillatorStringSetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesIdealSupportStringAndHarmonicLaws setup) :
    speedInMetersPerSecond setup.transverseWaveSpeed = 72 := by
  have h_harmonic := h_laws.fixedEndpointHarmonicLaw 4 (by norm_num)
    h_problem.pointPIsNode h_problem.pointQIsNode
    h_problem.requestedModeIsFourthHarmonic
  rw [h_problem.oscillatorFrequencyHertz, h_problem.separationMeters] at h_harmonic
  norm_num at h_harmonic
  linarith

/-!
Using `μ = 0.0016 kg/m`, `v = 72 m/s`, and `g = 9.8 m/s²`, the required
unrounded hanging mass is `5184 / 6125 kg`.
-/
lemma requiredHangingMass_exact
    (setup : OscillatorStringSetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesIdealSupportStringAndHarmonicLaws setup) :
    massInKilograms setup.hangingMass = 5184 / 6125 := by
  have h_speed := fourthHarmonicWaveSpeed_exact setup h_problem h_positive h_laws
  have h_wave := h_laws.transverseWaveSpeedLaw h_problem.stringTaut
  rw [h_speed, h_problem.linearDensityKilogramsPerMeter] at h_wave
  have h_argument_nonnegative :
      0 ≤ tensionInNewtons (setup.segmentTension .vibratingPQ) / (1 / 625 : ℝ) :=
    div_nonneg (le_of_lt (h_positive.segmentTensionsPositive .vibratingPQ))
      (by norm_num)
  have h_tension :
      tensionInNewtons (setup.segmentTension .vibratingPQ) = 5184 / 625 := by
    nlinarith [Real.sq_sqrt h_argument_nonnegative]
  have h_transmitted := h_laws.supportTransmitsTension
    h_laws.supportFrictionless h_laws.stringMassless
  have h_balance := h_laws.hangingMassStaticBalance h_laws.hangingMassStatic
  rw [h_gravity.gravityMetersPerSecondSquared] at h_balance
  norm_num at h_tension h_balance ⊢
  linarith

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed mass beside each answer label, in kilograms. -/
def AnswerChoice.massInKilograms : AnswerChoice → ℝ
  | .A => 764 / 1000
  | .B => 786 / 1000
  | .C => 815 / 1000
  | .D => 846 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a mass displayed to the nearest `0.001 kg`.  The tolerance is
`0.0005 kg`, half a unit in the last displayed digit.
-/
def MatchesAnswerChoice
    (setup : OscillatorStringSetup) (choice : AnswerChoice) : Prop :=
  abs (massInKilograms setup.hangingMass - choice.massInKilograms) ≤
    1 / 2000

/-!
The exact hanging mass required for the fourth harmonic agrees, at the
displayed precision, with recorded answer D: `0.846 kg`.

Blueprint: `thm:physics:phyx_mini_0298:target`.
-/
theorem problem_phyx_mini_0298
    (setup : OscillatorStringSetup)
    (h_problem : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesIdealSupportStringAndHarmonicLaws setup) :
    massInKilograms setup.hangingMass = 5184 / 6125 ∧
      MatchesAnswerChoice setup recordedAnswerChoice := by
  have h_mass := requiredHangingMass_exact setup h_problem h_gravity h_positive h_laws
  refine ⟨h_mass, ?_⟩
  norm_num [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.massInKilograms, h_mass,
    abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0298
