import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0105

open Dimension

/-!
# Polarized and unpolarized light passing through a rotating polarizer

A horizontally propagating beam is the incoherent superposition of an
unpolarized component of irradiance `I₀` and a linearly polarized component of
irradiance `Iₚ`.  The polarized component's plane is at the angle `θ` from the
vertical.  The graph plots the total transmitted irradiance against `α`, the
angle of an ideal polarizer's transmission axis from the vertical.

Irradiance is represented by a Physlib dimensionful quantity.  Power per area
has dimension `mass / time³`.  Real numbers below occur only as degree
coordinates, dimensionless trigonometric factors, and explicitly named SI
readouts in watts per square meter.
-/

/-- A nonnegative physical optical irradiance (power per area). -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The scalar SI readout of an irradiance, in watts per square meter. -/
def irradianceInWattsPerSquareMeter (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- The dimensionful irradiance whose SI readout is the supplied number. -/
def wattsPerSquareMeter (value : NNReal) : IrradianceQuantity :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- Convert a numerical degree coordinate from the graph into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Propagation direction stated in the problem text. -/
inductive PropagationDirection where
  | horizontal
  deriving DecidableEq, Repr

/-- The two labeled axes in the supplied scatter plot. -/
inductive FigureAxis where
  | polarizerAxisAngleAlpha
  | totalTransmittedIrradiance
  deriving DecidableEq, Repr

/-- The units printed beside the two graph axes. -/
inductive FigureAxisUnit where
  | degrees
  | wattsPerSquareMeter
  deriving DecidableEq, Repr

/-- Metadata and plotted ranges visible in the source graph. -/
structure PolarizerIntensityGraph where
  horizontalAxis : FigureAxis
  verticalAxis : FigureAxis
  horizontalUnit : FigureAxisUnit
  verticalUnit : FigureAxisUnit
  horizontalLower : ℝ
  horizontalUpper : ℝ
  verticalLower : ℝ
  verticalUpper : ℝ
  hasGrid : Bool

/-!
The physical components and figure-labeled quantities.  The arguments of the
three transmitted-irradiance functions are the plotted `α` coordinates in
degrees.  The polarized and unpolarized transmitted components are retained
separately so that the two governing transmission laws are explicit.
-/
structure MixedBeamPolarizerSetup where
  propagationDirection : PropagationDirection
  unpolarizedInputI0 : IrradianceQuantity
  polarizedInputIp : IrradianceQuantity
  polarizationPlaneTheta : Real.Angle
  unpolarizedAfterPolarizer : IrradianceQuantity
  polarizedAfterPolarizer : ℝ → IrradianceQuantity
  totalAfterPolarizer : ℝ → IrradianceQuantity
  graph : PolarizerIntensityGraph

/-- The textual setup fact that the incident beam travels horizontally. -/
def MatchesProblemDescription (setup : MixedBeamPolarizerSetup) : Prop :=
  setup.propagationDirection = .horizontal

/-!
The ideal-polarizer laws used by the problem.  An ideal polarizer transmits
half of an unpolarized component, a linearly polarized component obeys Malus's
law, and the two mutually incoherent transmitted irradiances add.  These laws
are stated for every polarizer angle and contain no numerical value for `Iₚ`.
-/
structure SatisfiesIdealPolarizerLaws
    (setup : MixedBeamPolarizerSetup) : Prop where
  unpolarizedTransmission :
    irradianceInWattsPerSquareMeter setup.unpolarizedAfterPolarizer =
      irradianceInWattsPerSquareMeter setup.unpolarizedInputI0 / 2
  malusTransmission : ∀ alphaDegrees : ℝ,
    irradianceInWattsPerSquareMeter
        (setup.polarizedAfterPolarizer alphaDegrees) =
      irradianceInWattsPerSquareMeter setup.polarizedInputIp *
        Real.Angle.cos
          (degrees alphaDegrees - setup.polarizationPlaneTheta) ^ 2
  incoherentAddition : ∀ alphaDegrees : ℝ,
    irradianceInWattsPerSquareMeter
        (setup.totalAfterPolarizer alphaDegrees) =
      irradianceInWattsPerSquareMeter setup.unpolarizedAfterPolarizer +
        irradianceInWattsPerSquareMeter
          (setup.polarizedAfterPolarizer alphaDegrees)

/-!
Calibrated readouts from the primary figure.  Its horizontal axis is `α` in
degrees from `0` to `200`; its vertical axis is total irradiance in `W/m²`
from `0` to `30`.  On that plotted interval the trace attains a maximum of
`25 W/m²` and a minimum of `5 W/m²`.  The auxiliary generated caption's
claim that the trough is near `10 W/m²` conflicts with the plotted points;
the primary image is used as required.  Neither extremum assumption states
the requested polarized-component irradiance.
-/
structure MatchesIntensityGraph (setup : MixedBeamPolarizerSetup) : Prop where
  horizontalAxis : setup.graph.horizontalAxis = .polarizerAxisAngleAlpha
  verticalAxis : setup.graph.verticalAxis = .totalTransmittedIrradiance
  horizontalUnit : setup.graph.horizontalUnit = .degrees
  verticalUnit : setup.graph.verticalUnit = .wattsPerSquareMeter
  horizontalRange :
    setup.graph.horizontalLower = 0 ∧ setup.graph.horizontalUpper = 200
  verticalRange :
    setup.graph.verticalLower = 0 ∧ setup.graph.verticalUpper = 30
  gridShown : setup.graph.hasGrid = true
  maximumReadout :
    (∃ alphaDegrees ∈ Set.Icc (0 : ℝ) 200,
      irradianceInWattsPerSquareMeter
          (setup.totalAfterPolarizer alphaDegrees) = 25) ∧
      ∀ alphaDegrees ∈ Set.Icc (0 : ℝ) 200,
        irradianceInWattsPerSquareMeter
            (setup.totalAfterPolarizer alphaDegrees) ≤ 25
  minimumReadout :
    (∃ alphaDegrees ∈ Set.Icc (0 : ℝ) 200,
      irradianceInWattsPerSquareMeter
          (setup.totalAfterPolarizer alphaDegrees) = 5) ∧
      ∀ alphaDegrees ∈ Set.Icc (0 : ℝ) 200,
        5 ≤ irradianceInWattsPerSquareMeter
          (setup.totalAfterPolarizer alphaDegrees)

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The irradiance readout in `W/m²` printed beside each answer choice. -/
def answerIrradianceInWattsPerSquareMeter : AnswerChoice → ℝ
  | .A => 20
  | .B => 15
  | .C => 25
  | .D => 30

/-- A choice matches the SI readout of the incident polarized component. -/
def MatchesPolarizedIntensityAnswer
    (setup : MixedBeamPolarizerSetup) (choice : AnswerChoice) : Prop :=
  irradianceInWattsPerSquareMeter setup.polarizedInputIp =
    answerIrradianceInWattsPerSquareMeter choice

/-!
The peak-to-trough variation is entirely due to the polarized component:
Malus's factor ranges from one to zero over the plotted interval.  Hence
`Iₚ = 25 - 5 = 20 W/m²`, selecting answer A.

Blueprint label: `thm:physics:phyx_mini_0105:target`.
-/
theorem problem_phyx_mini_0105
    (setup : MixedBeamPolarizerSetup)
    (_description : MatchesProblemDescription setup)
    (_laws : SatisfiesIdealPolarizerLaws setup)
    (_figure : MatchesIntensityGraph setup) :
    setup.polarizedInputIp = wattsPerSquareMeter 20 ∧
      MatchesPolarizedIntensityAnswer setup .A := by
  have orientation_in_graph (φ : Real.Angle) :
      ∃ alphaDegrees ∈ Set.Icc (0 : ℝ) 200,
        degrees alphaDegrees = φ ∨
          degrees alphaDegrees = φ + (Real.pi : Real.Angle) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    by_cases hφ : 0 ≤ φ.toReal
    · refine ⟨φ.toReal * 180 / Real.pi, ?_, Or.inl ?_⟩
      · constructor
        · positivity
        · apply (div_le_iff₀ hpi).2
          nlinarith [φ.toReal_le_pi]
      · simp [degrees, φ.coe_toReal]
    · have hφneg : φ.toReal < 0 := lt_of_not_ge hφ
      refine ⟨(φ.toReal + Real.pi) * 180 / Real.pi, ?_, Or.inr ?_⟩
      · constructor
        · apply (div_nonneg (mul_nonneg ?_ (by norm_num))) (le_of_lt hpi)
          linarith [φ.neg_pi_lt_toReal]
        · apply (div_le_iff₀ hpi).2
          nlinarith
      · simp [degrees, Real.Angle.coe_add, φ.coe_toReal]
  obtain ⟨alphaOne, halphaOne, hangleOne⟩ :=
    orientation_in_graph setup.polarizationPlaneTheta
  have hcosOne :
      Real.Angle.cos
          (degrees alphaOne - setup.polarizationPlaneTheta) ^ 2 = 1 := by
    rcases hangleOne with hangleOne | hangleOne
    · rw [hangleOne]
      simp [Real.Angle.cos_zero]
    · rw [hangleOne]
      simp
  obtain ⟨alphaZero, halphaZero, hangleZero⟩ :=
    orientation_in_graph
      (setup.polarizationPlaneTheta + (Real.pi / 2 : ℝ))
  have hcosZero :
      Real.Angle.cos
          (degrees alphaZero - setup.polarizationPlaneTheta) ^ 2 = 0 := by
    rcases hangleZero with hangleZero | hangleZero
    · rw [hangleZero]
      have hdiff :
          setup.polarizationPlaneTheta + (Real.pi / 2 : ℝ) -
              setup.polarizationPlaneTheta =
            ((Real.pi / 2 : ℝ) : Real.Angle) := by
        abel
      rw [hdiff, Real.Angle.cos_coe, Real.cos_pi_div_two]
      norm_num
    · rw [hangleZero]
      have hdiff :
          (setup.polarizationPlaneTheta + (Real.pi / 2 : ℝ)) +
                (Real.pi : Real.Angle) -
              setup.polarizationPlaneTheta =
            ((Real.pi / 2 : ℝ) : Real.Angle) + (Real.pi : Real.Angle) := by
        abel
      rw [hdiff, Real.Angle.cos_add_pi, Real.Angle.cos_coe,
        Real.cos_pi_div_two]
      norm_num
  let U : ℝ :=
    irradianceInWattsPerSquareMeter setup.unpolarizedAfterPolarizer
  let P : ℝ :=
    irradianceInWattsPerSquareMeter setup.polarizedInputIp
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, irradianceInWattsPerSquareMeter]
    positivity
  have hUP_le : U + P ≤ 25 := by
    have hbound := _figure.maximumReadout.2 alphaOne halphaOne
    rw [_laws.incoherentAddition alphaOne,
      _laws.malusTransmission alphaOne, hcosOne] at hbound
    simpa [U, P] using hbound
  have hU_ge : 5 ≤ U := by
    have hbound := _figure.minimumReadout.2 alphaZero halphaZero
    rw [_laws.incoherentAddition alphaZero,
      _laws.malusTransmission alphaZero, hcosZero] at hbound
    simpa [U] using hbound
  obtain ⟨alphaMax, _halphaMax, hmax⟩ :=
    _figure.maximumReadout.1
  have hUP_ge : 25 ≤ U + P := by
    have htotal := _laws.incoherentAddition alphaMax
    rw [_laws.malusTransmission alphaMax] at htotal
    have hcos_le :
        Real.Angle.cos
            (degrees alphaMax - setup.polarizationPlaneTheta) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg
        (Real.Angle.sin
          (degrees alphaMax - setup.polarizationPlaneTheta)),
        Real.Angle.cos_sq_add_sin_sq
          (degrees alphaMax - setup.polarizationPlaneTheta)]
    rw [hmax] at htotal
    dsimp [U, P]
    nlinarith
  obtain ⟨alphaMin, _halphaMin, hmin⟩ :=
    _figure.minimumReadout.1
  have hU_le : U ≤ 5 := by
    have htotal := _laws.incoherentAddition alphaMin
    rw [_laws.malusTransmission alphaMin] at htotal
    rw [hmin] at htotal
    have hcos_nonneg :
        0 ≤ Real.Angle.cos
            (degrees alphaMin - setup.polarizationPlaneTheta) ^ 2 :=
      sq_nonneg _
    dsimp [U, P]
    nlinarith
  have hP : P = 20 := by
    nlinarith
  have hIp :
      setup.polarizedInputIp = wattsPerSquareMeter 20 := by
    have hSI :
        setup.polarizedInputIp UnitChoices.SI =
          wattsPerSquareMeter 20 UnitChoices.SI := by
      apply WithDim.ext
      apply NNReal.eq
      simpa [P, irradianceInWattsPerSquareMeter, wattsPerSquareMeter,
        CarriesDimension.toDimensionful_apply_apply] using hP
    apply Dimensionful.ext
    funext units
    calc
      setup.polarizedInputIp units =
          UnitChoices.SI.dimScale units
              (dim (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)) •
            setup.polarizedInputIp UnitChoices.SI :=
        setup.polarizedInputIp.property UnitChoices.SI units
      _ = UnitChoices.SI.dimScale units
              (dim (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)) •
            wattsPerSquareMeter 20 UnitChoices.SI := by rw [hSI]
      _ = wattsPerSquareMeter 20 units :=
        ((wattsPerSquareMeter 20).property UnitChoices.SI units).symm
  refine ⟨hIp, ?_⟩
  simpa [MatchesPolarizedIntensityAnswer,
    answerIrradianceInWattsPerSquareMeter, P] using hP

end PhyXMiniProblems.ProblemPhyXMini0105
