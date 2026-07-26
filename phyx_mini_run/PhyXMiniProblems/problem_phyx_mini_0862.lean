import Mathlib
import Physlib.Electromagnetism.PointParticle.ThreeDimension
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0862

open Dimension
open scoped BigOperators

/-!
# Charge-magnitude ratio from a symmetric axial electric-field graph

Two point charges `q_a` and `q_b` lie on the physical `x`-axis at the distinct
positions labelled `a` and `b`.  The primary raster has three green branches,
vertical asymptotes at the two source positions, and mirror symmetry about the
midpoint.  Although the prose calls the ordinate the signed component `E_x`,
the raster only displays nonnegative heights.  We therefore interpret its
height as the magnitude of the coherent-SI `E_x` readout.

The governing point-charge field is grounded in Physlib's three-dimensional
distributional point-particle potential and electric-field theorem.  The
scalar profile used by the graph is the restriction of the theorem's ordinary
`q r / ‖r‖^3` profile to the `x`-axis, with coherent-SI charge and position
readouts.

Assumption/target split:

* governing laws: Physlib's static three-dimensional point-particle field and
  linear superposition, represented by the sum of the two axial source
  profiles;
* previous-part results: none;
* figure/data readouts: the `x`, `a`, and `b` labels, both dashed source lines,
  all three nonnegative green branches, the two asymptotes, and equal trace
  heights at a mirror pair of exterior sample points;
* current target conclusion: `|q_a / q_b| = 1`, corresponding to answer D.

No setup field, figure premise, or definition states an equality or ratio
between the two source charges.
-/

/-! ## Dimensionful quantities and coherent-SI scalar readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of an electric-field component. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A unit-independent signed electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent signed position coordinate on the physical `x`-axis. -/
abbrev AxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- Read a signed charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read an axial position in coherent-SI metres. -/
def positionInMeters (position : AxialPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Embed a metre coordinate as a point on the first axis of physical 3-space. -/
def xAxisPointInMeters (x : ℝ) : Space 3 :=
  ⟨fun i => if i = (0 : Fin 3) then x else 0⟩

/-! ## Source labels, graph vocabulary, and setup -/

/-- The two sources named by the labels under the dashed lines. -/
inductive ChargeSite where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- The text expected under each named source line. -/
def expectedPositionLabel : ChargeSite → String
  | .a => "a"
  | .b => "b"

/-- The two semantic axes of the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- The physical role assigned to a graph axis. -/
inductive GraphAxisRole where
  | axialPosition
  | electricFieldXComponentMagnitude
  deriving DecidableEq, Repr

/-- The three visible branches separated by the two source singularities. -/
inductive GraphBranch where
  | leftOfA
  | betweenAAndB
  | rightOfB
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data and an idealized scalar-height readout for image
`862.png`.  Heights are measured in the same numerical scale as newtons per
coulomb; their connection to the physical field is stated separately.
-/
structure ElectricFieldComponentFigure where
  axisRole : GraphAxis → GraphAxisRole
  printedAxisLabel : GraphAxis → Option String
  verticalDashedLineShown : ChargeSite → Bool
  printedChargePositionLabel : ChargeSite → String
  dashedLineMeterCoordinate : ChargeSite → ℝ
  greenBranchShown : GraphBranch → Bool
  traceLiesAboveHorizontalAxis : Bool
  dashedLineIsVerticalAsymptote : ChargeSite → Bool
  traceAppearsMirrorSymmetric : Bool
  traceHeightInNewtonsPerCoulombAtMeter : ℝ → ℝ

/-!
The free-space medium, dimensionful source data, primary figure, and a pair of
independent exterior sample positions used to read the pictured symmetry.
-/
structure TwoPointChargeXAxisSetup where
  freeSpace : Electromagnetism.FreeSpace
  charge : ChargeSite → SignedChargeQuantity
  position : ChargeSite → AxialPositionQuantity
  figure : ElectricFieldComponentFigure
  leftExteriorSample : AxialPositionQuantity
  rightExteriorSample : AxialPositionQuantity

/-! ## Physlib point-particle grounding and axial SI profile -/

/-- The stationary 3D point-particle potential attached to a named source. -/
def sourcePointChargePotential
    (setup : TwoPointChargeXAxisSetup) (source : ChargeSite) :
    Electromagnetism.DistElectromagneticPotential 3 :=
  Electromagnetism.DistElectromagneticPotential.threeDimPointParticle
    setup.freeSpace
    (chargeInCoulombs (setup.charge source))
    (xAxisPointInMeters (positionInMeters (setup.position source)))

/-- The sum of the two stationary point-particle potentials. -/
def netPointChargePotential (setup : TwoPointChargeXAxisSetup) :
    Electromagnetism.DistElectromagneticPotential 3 :=
  ∑ source : ChargeSite, sourcePointChargePotential setup source

/-!
An exact specialization of Physlib's theorem giving the distributional
electric field of each source.  This declaration records the library law used
to ground the ordinary axial readout below; it introduces no new axiom.
-/
def physlibSourcePointChargeElectricFieldLaw
    (setup : TwoPointChargeXAxisSetup) (source : ChargeSite) :=
  Electromagnetism.DistElectromagneticPotential.threeDimPointParticle_electricField
    setup.freeSpace
    (chargeInCoulombs (setup.charge source))
    (xAxisPointInMeters (positionInMeters (setup.position source)))

/--
The ordinary vector profile occurring inside Physlib's distributional
point-charge field theorem, with coherent-SI source data.
-/
def sourcePointChargeElectricFieldOrdinaryProfile
    (setup : TwoPointChargeXAxisSetup) (source : ChargeSite)
    (point : Space 3) : EuclideanSpace ℝ (Fin 3) :=
  (chargeInCoulombs (setup.charge source) /
      (4 * Real.pi * setup.freeSpace.ε₀)) •
    (‖point - xAxisPointInMeters
        (positionInMeters (setup.position source))‖ ^ (-3 : ℤ) •
      Space.basis.repr
        (point - xAxisPointInMeters
          (positionInMeters (setup.position source))))

/-- The free-space Coulomb constant in coherent SI, `N m² / C²`. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (setup : TwoPointChargeXAxisSetup) : ℝ :=
  Electromagnetism.EMSystem.coulombConstant
    { ε₀ := setup.freeSpace.ε₀, μ₀ := setup.freeSpace.μ₀ }

/-- Metre displacement from a source to an axial observation point. -/
def displacementFromSourceInMeters
    (setup : TwoPointChargeXAxisSetup)
    (source : ChargeSite) (point : AxialPositionQuantity) : ℝ :=
  positionInMeters point - positionInMeters (setup.position source)

/-!
The signed coherent-SI x-component of one source's field.  It is the x-axis
restriction of Physlib's three-dimensional point-particle profile
`q r / ‖r‖³`.
-/
def sourceAxialElectricFieldInNewtonsPerCoulomb
    (setup : TwoPointChargeXAxisSetup)
    (source : ChargeSite) (point : AxialPositionQuantity) : ℝ :=
  sourcePointChargeElectricFieldOrdinaryProfile setup source
    (xAxisPointInMeters (positionInMeters point)) 0

/-!
On the x-axis, the Physlib ordinary vector profile reduces to the familiar
signed scalar form `k q (x-x₀) / |x-x₀|³`.
-/
lemma source_axial_profile_eq_coulomb_formula
    (setup : TwoPointChargeXAxisSetup)
    (source : ChargeSite) (point : AxialPositionQuantity) :
    sourceAxialElectricFieldInNewtonsPerCoulomb setup source point =
      coulombConstantInNewtonMetersSquaredPerCoulombSquared setup *
        chargeInCoulombs (setup.charge source) *
        displacementFromSourceInMeters setup source point /
        |displacementFromSourceInMeters setup source point| ^ 3 := by
  have hnorm (x y : ℝ) :
      ‖xAxisPointInMeters x - xAxisPointInMeters y‖ = |x - y| := by
    rw [Space.norm_eq]
    simp [xAxisPointInMeters, Fin.sum_univ_succ, Real.sqrt_sq_eq_abs]
  rw [sourceAxialElectricFieldInNewtonsPerCoulomb,
    sourcePointChargeElectricFieldOrdinaryProfile]
  rw [hnorm]
  change
    chargeInCoulombs (setup.charge source) /
          (4 * Real.pi * setup.freeSpace.ε₀) *
        (|positionInMeters point -
              positionInMeters (setup.position source)| ^ (-3 : ℤ) *
          (positionInMeters point -
            positionInMeters (setup.position source))) =
      _
  have hzpow :
      |positionInMeters point -
            positionInMeters (setup.position source)| ^ (-3 : ℤ) =
        |positionInMeters point -
            positionInMeters (setup.position source)|⁻¹ ^ (3 : ℕ) := by
    rw [zpow_neg]
    exact (inv_pow _ 3).symm
  rw [hzpow]
  simp [coulombConstantInNewtonMetersSquaredPerCoulombSquared,
    displacementFromSourceInMeters,
    Electromagnetism.EMSystem.coulombConstant]
  ring

/-- Linear superposition of the two signed axial point-charge fields. -/
def netAxialElectricFieldInNewtonsPerCoulomb
    (setup : TwoPointChargeXAxisSetup)
    (point : AxialPositionQuantity) : ℝ :=
  ∑ source : ChargeSite,
    sourceAxialElectricFieldInNewtonsPerCoulomb setup source point

/-! ## Physical geometry and primary-image evidence -/

/-!
The charges are distinct and nonzero, and the two chosen samples are exterior
points reflected through the midpoint of `a` and `b`.  These hypotheses make
the requested ratio well-defined without assuming its value.
-/
structure HasSymmetricExteriorSampleGeometry
    (setup : TwoPointChargeXAxisSetup) : Prop where
  aIsLeftOfB :
    positionInMeters (setup.position .a) <
      positionInMeters (setup.position .b)
  leftSampleIsExterior :
    positionInMeters setup.leftExteriorSample <
      positionInMeters (setup.position .a)
  rightSampleIsExterior :
    positionInMeters (setup.position .b) <
      positionInMeters setup.rightExteriorSample
  samplesAreMirrorImages :
    positionInMeters setup.leftExteriorSample +
        positionInMeters setup.rightExteriorSample =
      positionInMeters (setup.position .a) +
        positionInMeters (setup.position .b)
  chargeANonzero : chargeInCoulombs (setup.charge .a) ≠ 0
  chargeBNonzero : chargeInCoulombs (setup.charge .b) ≠ 0

/-!
Literal raster features plus the idealized equal-height readout at the chosen
mirror pair.  This predicate contains no charge or charge-ratio equality.
-/
structure MatchesSuppliedElectricFieldGraph
    (setup : TwoPointChargeXAxisSetup) : Prop where
  horizontalAxisRole :
    setup.figure.axisRole .horizontal = .axialPosition
  verticalAxisRole :
    setup.figure.axisRole .vertical = .electricFieldXComponentMagnitude
  horizontalAxisLabel :
    setup.figure.printedAxisLabel .horizontal = some "x"
  verticalAxisHasNoPrintedLabel :
    setup.figure.printedAxisLabel .vertical = none
  bothDashedSourceLinesShown :
    ∀ source, setup.figure.verticalDashedLineShown source = true
  printedSourceLabels :
    ∀ source,
      setup.figure.printedChargePositionLabel source =
        expectedPositionLabel source
  dashedLinesAtChargePositions :
    ∀ source,
      setup.figure.dashedLineMeterCoordinate source =
        positionInMeters (setup.position source)
  allThreeGreenBranchesShown :
    ∀ branch, setup.figure.greenBranchShown branch = true
  traceIsAboveAxis : setup.figure.traceLiesAboveHorizontalAxis = true
  traceHeightNonnegative :
    ∀ x, 0 ≤ setup.figure.traceHeightInNewtonsPerCoulombAtMeter x
  bothSourceAsymptotesShown :
    ∀ source, setup.figure.dashedLineIsVerticalAsymptote source = true
  visualMirrorSymmetry : setup.figure.traceAppearsMirrorSymmetric = true
  symmetricExteriorTraceHeights :
    setup.figure.traceHeightInNewtonsPerCoulombAtMeter
        (positionInMeters setup.leftExteriorSample) =
      setup.figure.traceHeightInNewtonsPerCoulombAtMeter
        (positionInMeters setup.rightExteriorSample)

/-!
The prose identifies the plotted profile with `E_x`; because the raster has
only nonnegative heights, its ordinate is calibrated to the magnitude of the
signed net component.  This is a figure-to-physics calibration, not an answer
premise.
-/
structure TraceHeightCalibratesAxialFieldMagnitude
    (setup : TwoPointChargeXAxisSetup) : Prop where
  leftSampleCalibration :
    setup.figure.traceHeightInNewtonsPerCoulombAtMeter
        (positionInMeters setup.leftExteriorSample) =
      |netAxialElectricFieldInNewtonsPerCoulomb
        setup setup.leftExteriorSample|
  rightSampleCalibration :
    setup.figure.traceHeightInNewtonsPerCoulombAtMeter
        (positionInMeters setup.rightExteriorSample) =
      |netAxialElectricFieldInNewtonsPerCoulomb
        setup setup.rightExteriorSample|

/-! ## Derived relations and multiple-choice target -/

/-- The mirror sample readouts give equal magnitudes of the net axial field. -/
lemma symmetric_sample_field_magnitudes_equal
    (setup : TwoPointChargeXAxisSetup)
    (_figure : MatchesSuppliedElectricFieldGraph setup)
    (_calibration : TraceHeightCalibratesAxialFieldMagnitude setup) :
    |netAxialElectricFieldInNewtonsPerCoulomb
        setup setup.leftExteriorSample| =
      |netAxialElectricFieldInNewtonsPerCoulomb
        setup setup.rightExteriorSample| := by
  simpa only [_calibration.leftSampleCalibration,
    _calibration.rightSampleCalibration] using
    _figure.symmetricExteriorTraceHeights

/-!
For two nonzero point charges at mirror exterior samples, the equal field
magnitudes force equality of the source-charge magnitudes.
-/
lemma charge_readout_magnitudes_equal
    (setup : TwoPointChargeXAxisSetup)
    (_geometry : HasSymmetricExteriorSampleGeometry setup)
    (_figure : MatchesSuppliedElectricFieldGraph setup)
    (_calibration : TraceHeightCalibratesAxialFieldMagnitude setup) :
    |chargeInCoulombs (setup.charge .a)| =
      |chargeInCoulombs (setup.charge .b)| := by
  set_option maxHeartbeats 1000000 in
    let a : ℝ := positionInMeters (setup.position .a)
    let b : ℝ := positionInMeters (setup.position .b)
    let l : ℝ := positionInMeters setup.leftExteriorSample
    let r : ℝ := positionInMeters setup.rightExteriorSample
    let qa : ℝ := chargeInCoulombs (setup.charge .a)
    let qb : ℝ := chargeInCoulombs (setup.charge .b)
    let k : ℝ :=
      coulombConstantInNewtonMetersSquaredPerCoulombSquared setup
    have hab : a < b := _geometry.aIsLeftOfB
    have hla : l < a := _geometry.leftSampleIsExterior
    have hbr : b < r := _geometry.rightSampleIsExterior
    have hmirror : l + r = a + b := _geometry.samplesAreMirrorImages
    have hlb : l < b := lt_trans hla hab
    have har : a < r := lt_trans hab hbr
    have hlefta : l - a < 0 := sub_neg.mpr hla
    have hleftb : l - b < 0 := sub_neg.mpr hlb
    have hrighta : 0 < r - a := sub_pos.mpr har
    have hrightb : 0 < r - b := sub_pos.mpr hbr
    have hra : r - a = b - l := by
      linarith
    have hrb : r - b = a - l := by
      linarith
    have hkpos : 0 < k := by
      dsimp [k, coulombConstantInNewtonMetersSquaredPerCoulombSquared,
        Electromagnetism.EMSystem.coulombConstant]
      exact one_div_pos.mpr
        (mul_pos (mul_pos (by norm_num) Real.pi_pos)
          setup.freeSpace.ε₀_pos)
    have hk : k ≠ 0 := ne_of_gt hkpos
    have hfield :=
      symmetric_sample_field_magnitudes_equal setup _figure _calibration
    simp only [netAxialElectricFieldInNewtonsPerCoulomb] at hfield
    rw [show (Finset.univ : Finset ChargeSite) = {.a, .b} by decide]
      at hfield
    simp_rw [source_axial_profile_eq_coulomb_formula] at hfield
    simp at hfield
    change
      |k * qa * (l - a) / |l - a| ^ 3 +
          k * qb * (l - b) / |l - b| ^ 3| =
        |k * qa * (r - a) / |r - a| ^ 3 +
          k * qb * (r - b) / |r - b| ^ 3|
      at hfield
    rw [abs_of_neg hlefta, abs_of_neg hleftb,
      abs_of_pos hrighta, abs_of_pos hrightb, hra, hrb] at hfield
    have hla_neg : l - a = -(a - l) := by ring
    have hlb_neg : l - b = -(b - l) := by ring
    rw [hla_neg, hlb_neg] at hfield
    generalize hd_def : a - l = d at hfield
    generalize he_def : b - l = e at hfield
    simp only [neg_neg] at hfield
    have hd : 0 < d := by
      linarith
    have he : 0 < e := by
      linarith
    have hde : d < e := by
      linarith
    have hd0 : d ≠ 0 := ne_of_gt hd
    have he0 : e ≠ 0 := ne_of_gt he
    have h1 :
        k * qa * -d / d ^ 3 = -k * qa / d ^ 2 := by
      field_simp [hd0]
    have h2 :
        k * qb * -e / e ^ 3 = -k * qb / e ^ 2 := by
      field_simp [he0]
    have h3 :
        k * qa * e / e ^ 3 = k * qa / e ^ 2 := by
      field_simp [he0]
    have h4 :
        k * qb * d / d ^ 3 = k * qb / d ^ 2 := by
      field_simp [hd0]
    rw [h1, h2, h3, h4] at hfield
    have hpow : d ^ 4 < e ^ 4 :=
      pow_lt_pow_left₀ hde hd.le (by norm_num)
    have hsq := congrArg (fun x : ℝ => x ^ 2) hfield
    simp only [sq_abs] at hsq
    field_simp [hd0, he0] at hsq
    have hchargesq : qa ^ 2 = qb ^ 2 := by
      nlinarith
    change |qa| = |qb|
    nlinarith [sq_abs qa, sq_abs qb, abs_nonneg qa, abs_nonneg qb]

/-- Labels attached to the four ratio choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless ratio printed beside each choice. -/
def AnswerChoice.ratio : AnswerChoice → ℝ
  | .A => 6 / 5
  | .B => 7 / 5
  | .C => 2
  | .D => 1

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
**Blueprint target** `thm:physics:phyx_mini_0862:target`.

The symmetric magnitude profile of the superposed Physlib point-charge fields
forces the two source charges to have equal magnitudes.  Since `q_b` is
nonzero, the requested dimensionless ratio is `1`, the value of answer D.
-/
theorem problem_phyx_mini_0862
    (setup : TwoPointChargeXAxisSetup)
    (_geometry : HasSymmetricExteriorSampleGeometry setup)
    (_figure : MatchesSuppliedElectricFieldGraph setup)
    (_calibration : TraceHeightCalibratesAxialFieldMagnitude setup) :
    |chargeInCoulombs (setup.charge .a) /
        chargeInCoulombs (setup.charge .b)| = 1 := by
  rw [abs_div,
    charge_readout_magnitudes_equal setup _geometry _figure _calibration]
  exact div_self (abs_ne_zero.mpr _geometry.chargeBNonzero)

end PhyXMiniProblems.ProblemPhyXMini0862
