import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

/-!
# PhyX mini problem 0522: two collinear electric dipoles

The primary image shows two identical horizontal dipoles.  In each dipole the
positive charge is the left endpoint and the negative charge is the right
endpoint.  Their common within-dipole separation is `d`, and the centers of
the dipoles are separated by `r`.

The formalization keeps charge, length, dipole moment, vacuum permittivity,
and energy dimensionful.  It models the exact four cross-dipole Coulomb
interactions as a function of center separation.  The inverse-cube far-field
coefficient is then characterized by an asymptotic limit rather than assumed
to have the value requested by the problem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0522

open Dimension
open scoped BigOperators Topology

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- The physical dimension of an electric dipole moment, charge times length. -/
def electricDipoleMomentDimension : Dimension := C𝓭 * L𝓭

/-- A nonnegative electric-dipole-moment magnitude. -/
abbrev ElectricDipoleMomentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricDipoleMomentDimension NNReal)

/-!
Vacuum permittivity has dimension `C² T² M⁻¹ L⁻³`, equivalently charge
squared divided by energy times length.
-/
def vacuumPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative physical vacuum permittivity. -/
abbrev VacuumPermittivityQuantity : Type :=
  Dimensionful (WithDim vacuumPermittivityDimension NNReal)

/-- SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Charge-magnitude readout in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Electric-dipole-moment readout in coulomb-metres. -/
def dipoleMomentMagnitudeInCoulombMeters
    (moment : ElectricDipoleMomentMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout moment

/-- Vacuum-permittivity readout in farads per metre. -/
def vacuumPermittivityInFaradsPerMeter
    (permittivity : VacuumPermittivityQuantity) : ℝ :=
  nonnegativeSIReadout permittivity

/-- Signed energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical labels and primary-figure metadata -/

/-- The two dipoles in their left-to-right order in the image. -/
inductive DipoleLabel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two endpoints of a horizontal dipole. -/
inductive DipoleEnd where
  | leftEnd
  | rightEnd
  deriving DecidableEq, Fintype, Repr

/-- The sign carried by a point charge. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- The distance symbols named by the prose and the primary image. -/
inductive SeparationLabel where
  | d
  | r
  deriving DecidableEq, Repr

/-- The scalar multiplier associated with a charge sign. -/
def chargeSignFactor : ChargeSign → ℝ
  | .positive => 1
  | .negative => -1

/-!
Literal visual metadata from the primary raster.  The `r` arrow is drawn
between dashed center lines and contains a break indicating a long distance.
-/
structure DipolePairFigure where
  shownChargeSign : DipoleLabel → DipoleEnd → ChargeSign
  connectorShown : DipoleLabel → Bool
  centerGuideShown : DipoleLabel → Bool
  centerSeparationArrowShown : Bool
  centerSeparationLabel : SeparationLabel
  longDistanceBreakShown : Bool

/-!
The physical system and its response quantities.

The interaction profile is an SI scalar readout indexed by a center separation
in metres.  Its name records both the physical observable and its unit.  The
far-field coefficient likewise has the dimensional role joule-metres cubed.
Neither field is assigned the coefficient sought in the question.
-/
structure CollinearDipolePairSetup where
  chargeMagnitude : DipoleLabel → ChargeMagnitudeQuantity
  chargeSignAt : DipoleLabel → DipoleEnd → ChargeSign
  withinDipoleSeparation : DipoleLabel → LengthQuantity
  dipoleMomentMagnitude : DipoleLabel → ElectricDipoleMomentMagnitudeQuantity
  centerSeparation : LengthQuantity
  vacuumPermittivity : VacuumPermittivityQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  internalPotentialEnergy : DimEnergy
  interactionPotentialEnergyInJoulesAtCenterSeparation : ℝ → ℝ
  farFieldInteractionCoefficientInJouleMeterCubed : ℝ
  farFieldPotentialEnergy : DimEnergy
  figure : DipolePairFigure

/-! ## Collinear geometry and exact pairwise Coulomb sums -/

/-- Center coordinate, in metres, when the left center is chosen as the origin. -/
def dipoleCenterInMeters (centerSeparationInMeters : ℝ) : DipoleLabel → ℝ
  | .left => 0
  | .right => centerSeparationInMeters

/-- Signed endpoint offset from a dipole's center. -/
def endpointOffsetInMeters
    (setup : CollinearDipolePairSetup)
    (dipole : DipoleLabel) : DipoleEnd → ℝ
  | .leftEnd => -lengthInMeters (setup.withinDipoleSeparation dipole) / 2
  | .rightEnd => lengthInMeters (setup.withinDipoleSeparation dipole) / 2

/-- Axial position of a labeled charge endpoint in the collinear model. -/
def chargePositionInMeters
    (setup : CollinearDipolePairSetup)
    (centerSeparationInMeters : ℝ)
    (dipole : DipoleLabel)
    (dipoleEnd : DipoleEnd) : ℝ :=
  dipoleCenterInMeters centerSeparationInMeters dipole +
    endpointOffsetInMeters setup dipole dipoleEnd

/-- Distance between two labeled point charges at a proposed center separation. -/
def pointChargeDistanceInMeters
    (setup : CollinearDipolePairSetup)
    (centerSeparationInMeters : ℝ)
    (firstDipole : DipoleLabel)
    (firstEnd : DipoleEnd)
    (secondDipole : DipoleLabel)
    (secondEnd : DipoleEnd) : ℝ :=
  |chargePositionInMeters setup centerSeparationInMeters firstDipole firstEnd -
    chargePositionInMeters setup centerSeparationInMeters secondDipole secondEnd|

/-- Signed SI charge at one endpoint of a dipole. -/
def signedChargeInCoulombs
    (setup : CollinearDipolePairSetup)
    (dipole : DipoleLabel)
    (dipoleEnd : DipoleEnd) : ℝ :=
  chargeSignFactor (setup.chargeSignAt dipole dipoleEnd) *
    chargeMagnitudeInCoulombs (setup.chargeMagnitude dipole)

/-!
The exact internal Coulomb energy of the two `(+q,-q)` pairs.  Each unordered
within-dipole pair occurs exactly once.
-/
def internalCoulombEnergyInJoules
    (setup : CollinearDipolePairSetup) : ℝ :=
  ∑ dipole : DipoleLabel,
    setup.electromagneticSystem.coulombConstant *
        signedChargeInCoulombs setup dipole .leftEnd *
        signedChargeInCoulombs setup dipole .rightEnd /
      pointChargeDistanceInMeters setup 0 dipole .leftEnd dipole .rightEnd

/-!
The exact cross-dipole Coulomb energy at center separation `R`.  The nested
sum contains the four pairs formed from one endpoint of each dipole.
-/
def crossDipoleCoulombEnergyInJoules
    (setup : CollinearDipolePairSetup)
    (centerSeparationInMeters : ℝ) : ℝ :=
  ∑ leftEndpoint : DipoleEnd, ∑ rightEndpoint : DipoleEnd,
    setup.electromagneticSystem.coulombConstant *
        signedChargeInCoulombs setup .left leftEndpoint *
        signedChargeInCoulombs setup .right rightEndpoint /
      pointChargeDistanceInMeters setup centerSeparationInMeters
        .left leftEndpoint .right rightEndpoint

/-! ## Problem data, scale separation, and governing laws -/

/-!
Data read from the prose and primary image.  In particular, both dipoles have
`+q` on the left and `-q` on the right, and the arrow labeled `r` measures the
center-to-center separation.  This predicate contains no energy formula.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : CollinearDipolePairSetup) : Prop where
  positiveChargesOnLeft :
    ∀ dipole, setup.chargeSignAt dipole .leftEnd = .positive
  negativeChargesOnRight :
    ∀ dipole, setup.chargeSignAt dipole .rightEnd = .negative
  figureShowsPhysicalSigns :
    ∀ dipole dipoleEnd,
      setup.figure.shownChargeSign dipole dipoleEnd =
        setup.chargeSignAt dipole dipoleEnd
  bothDipoleConnectorsShown :
    ∀ dipole, setup.figure.connectorShown dipole = true
  bothCenterGuidesShown :
    ∀ dipole, setup.figure.centerGuideShown dipole = true
  centerDistanceArrowShown : setup.figure.centerSeparationArrowShown = true
  centerDistanceLabeledR : setup.figure.centerSeparationLabel = .r
  longDistanceBreakShown : setup.figure.longDistanceBreakShown = true
  identicalChargeMagnitudes :
    setup.chargeMagnitude .left = setup.chargeMagnitude .right
  identicalWithinDipoleSeparations :
    setup.withinDipoleSeparation .left =
      setup.withinDipoleSeparation .right
  identicalDipoleMomentMagnitudes :
    setup.dipoleMomentMagnitude .left =
      setup.dipoleMomentMagnitude .right

/-- Positivity and non-overlap conditions for the physical parameters. -/
structure HasPhysicalDipoleParameters
    (setup : CollinearDipolePairSetup) : Prop where
  chargeMagnitudePositive :
    ∀ dipole, 0 < chargeMagnitudeInCoulombs (setup.chargeMagnitude dipole)
  withinDipoleSeparationPositive :
    ∀ dipole, 0 < lengthInMeters (setup.withinDipoleSeparation dipole)
  dipoleMomentMagnitudePositive :
    ∀ dipole,
      0 < dipoleMomentMagnitudeInCoulombMeters
        (setup.dipoleMomentMagnitude dipole)
  centerSeparationPositive : 0 < lengthInMeters setup.centerSeparation
  vacuumPermittivityPositive :
    0 < vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity
  dipolesDoNotOverlap :
    ∀ dipole,
      lengthInMeters (setup.withinDipoleSeparation dipole) <
        lengthInMeters setup.centerSeparation

/-!
A quantitative witness for the qualitative condition `r ≫ d`.  The modeler
chooses a dimensionless tolerance smaller than one, and each ratio `d/r` must
lie below it.  No numerical tolerance is invented from the raster.
-/
structure IsFarFieldRegime
    (setup : CollinearDipolePairSetup)
    (dimensionlessTolerance : ℝ) : Prop where
  tolerancePositive : 0 < dimensionlessTolerance
  toleranceLessThanOne : dimensionlessTolerance < 1
  separationRatioBound :
    ∀ dipole,
      lengthInMeters (setup.withinDipoleSeparation dipole) /
          lengthInMeters setup.centerSeparation ≤
        dimensionlessTolerance

/-!
Coulomb's law, the definition `p = qd`, and the convention used to extract a
far-field prediction from the exact interaction profile.

The asymptotic field merely says that the stored coefficient is the limit of
`R³ U_interaction(R)`.  It does not state that limit's value.  Similarly, the
assembly field only says that the far-field prediction consists of the exact
internal energy plus the extracted inverse-cube term.
-/
structure SatisfiesCoulombDipoleLaws
    (setup : CollinearDipolePairSetup) : Prop where
  permittivityMatchesPhyslibSystem :
    setup.electromagneticSystem.ε₀ =
      vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity
  dipoleMomentIsChargeTimesSeparation :
    ∀ dipole,
      dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude dipole) =
        chargeMagnitudeInCoulombs (setup.chargeMagnitude dipole) *
          lengthInMeters (setup.withinDipoleSeparation dipole)
  internalEnergyFromPairwiseCoulombLaw :
    energyInJoules setup.internalPotentialEnergy =
      internalCoulombEnergyInJoules setup
  interactionProfileFromPairwiseCoulombLaw :
    ∀ centerSeparationInMeters : ℝ,
      (∀ dipole,
        lengthInMeters (setup.withinDipoleSeparation dipole) <
          centerSeparationInMeters) →
      setup.interactionPotentialEnergyInJoulesAtCenterSeparation
          centerSeparationInMeters =
        crossDipoleCoulombEnergyInJoules setup centerSeparationInMeters
  farFieldCoefficientFromAsymptoticLimit :
    Filter.Tendsto
      (fun centerSeparationInMeters : ℝ =>
        centerSeparationInMeters ^ 3 *
          setup.interactionPotentialEnergyInJoulesAtCenterSeparation
            centerSeparationInMeters)
      Filter.atTop
      (nhds setup.farFieldInteractionCoefficientInJouleMeterCubed)
  farFieldEnergyAssembly :
    energyInJoules setup.farFieldPotentialEnergy =
      energyInJoules setup.internalPotentialEnergy +
        setup.farFieldInteractionCoefficientInJouleMeterCubed /
          lengthInMeters setup.centerSeparation ^ 3

/-! ## Displayed choices -/

/-- Labels printed beside the four multiple-choice formulas. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The energy expression printed for each answer choice, evaluated using the
common dipole data represented by the left dipole.
-/
def displayedAnswerEnergyInJoules
    (setup : CollinearDipolePairSetup) : AnswerChoice → ℝ
  | .A =>
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (3 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters setup.centerSeparation ^ 3) -
        2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (3 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters (setup.withinDipoleSeparation .left) ^ 3)
  | .B =>
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (3 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters setup.centerSeparation ^ 3) +
        2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (3 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters (setup.withinDipoleSeparation .left) ^ 3)
  | .C =>
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters setup.centerSeparation ^ 3) +
        2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters (setup.withinDipoleSeparation .left) ^ 3)
  | .D =>
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters setup.centerSeparation ^ 3) -
        2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters (setup.withinDipoleSeparation .left) ^ 3)

/-- A displayed choice is correct when it equals the modeled far-field energy. -/
def IsCorrectAnswer
    (setup : CollinearDipolePairSetup)
    (choice : AnswerChoice) : Prop :=
  energyInJoules setup.farFieldPotentialEnergy =
    displayedAnswerEnergyInJoules setup choice

/-! ## Derived targets -/

/-!
The two attractive within-dipole Coulomb pairs give the constant internal
contribution appearing in the recorded answer.
-/
lemma internalPotentialEnergy_formula
    (setup : CollinearDipolePairSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalDipoleParameters setup)
    (h_laws : SatisfiesCoulombDipoleLaws setup) :
    energyInJoules setup.internalPotentialEnergy =
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
        (4 * Real.pi *
          vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
          lengthInMeters (setup.withinDipoleSeparation .left) ^ 3) := by
  rw [h_laws.internalEnergyFromPairwiseCoulombLaw]
  classical
  unfold internalCoulombEnergyInJoules
  have h_univ :
      (Finset.univ : Finset DipoleLabel) = {.left, .right} := by
    decide
  rw [h_univ]
  have hd_right :
      0 < lengthInMeters (setup.withinDipoleSeparation .right) :=
    h_physical.withinDipoleSeparationPositive .right
  have h_internal_distance :
      |-lengthInMeters (setup.withinDipoleSeparation .right) / 2 -
          lengthInMeters (setup.withinDipoleSeparation .right) / 2| =
        lengthInMeters (setup.withinDipoleSeparation .right) := by
    rw [show
      -lengthInMeters (setup.withinDipoleSeparation .right) / 2 -
          lengthInMeters (setup.withinDipoleSeparation .right) / 2 =
        -lengthInMeters (setup.withinDipoleSeparation .right) by ring]
    rw [abs_neg, abs_of_pos hd_right]
  have h_permittivity :=
    h_physical.vacuumPermittivityPositive
  simp [signedChargeInCoulombs, h_figure.positiveChargesOnLeft,
    h_figure.negativeChargesOnRight, chargeSignFactor,
    pointChargeDistanceInMeters, chargePositionInMeters,
    dipoleCenterInMeters, endpointOffsetInMeters, h_internal_distance,
    h_figure.identicalChargeMagnitudes,
    h_figure.identicalWithinDipoleSeparations,
    Electromagnetism.EMSystem.coulombConstant,
    h_laws.permittivityMatchesPhyslibSystem,
    h_laws.dipoleMomentIsChargeTimesSeparation]
  field_simp
  ring

/-!
The exact four-pair interaction profile has inverse-cube coefficient
`-2 p²/(4π ε₀)` for the parallel collinear orientation in the image.
-/
lemma farFieldInteractionCoefficient_formula
    (setup : CollinearDipolePairSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalDipoleParameters setup)
    (h_laws : SatisfiesCoulombDipoleLaws setup) :
    setup.farFieldInteractionCoefficientInJouleMeterCubed =
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
        (4 * Real.pi *
          vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity) := by
  classical
  have h_univ_end :
      (Finset.univ : Finset DipoleEnd) = {.leftEnd, .rightEnd} := by
    decide
  have hd :
      0 < lengthInMeters (setup.withinDipoleSeparation .right) :=
    h_physical.withinDipoleSeparationPositive .right
  have h_event :
      ∀ᶠ R : ℝ in Filter.atTop,
        lengthInMeters (setup.withinDipoleSeparation .right) < R :=
    (Filter.tendsto_id :
      Filter.Tendsto (fun x : ℝ => x) Filter.atTop Filter.atTop
    ).eventually_gt_atTop _
  have h_profile :
      ∀ᶠ R : ℝ in Filter.atTop,
        R ^ 3 *
            setup.interactionPotentialEnergyInJoulesAtCenterSeparation R =
          (-2 * setup.electromagneticSystem.coulombConstant *
              chargeMagnitudeInCoulombs
                  (setup.chargeMagnitude .right) ^ 2 *
              lengthInMeters
                  (setup.withinDipoleSeparation .right) ^ 2) /
            (1 -
              lengthInMeters
                  (setup.withinDipoleSeparation .right) ^ 2 / R ^ 2) := by
    filter_upwards [h_event] with R hRd
    have hR : 0 < R := lt_trans hd hRd
    have hplus :
        0 < R +
          lengthInMeters (setup.withinDipoleSeparation .right) := by
      linarith
    have hminus :
        0 < R -
          lengthInMeters (setup.withinDipoleSeparation .right) :=
      sub_pos.mpr hRd
    have hsquare :
        lengthInMeters (setup.withinDipoleSeparation .right) ^ 2 <
          R ^ 2 := by
      nlinarith
    have hquad :
        R ^ 2 -
            lengthInMeters
                (setup.withinDipoleSeparation .right) ^ 2 ≠ 0 :=
      ne_of_gt (sub_pos.mpr hsquare)
    have hdist_ll :
        pointChargeDistanceInMeters setup R
            .left .leftEnd .right .leftEnd = R := by
      simp [pointChargeDistanceInMeters, chargePositionInMeters,
        dipoleCenterInMeters, endpointOffsetInMeters,
        h_figure.identicalWithinDipoleSeparations]
      exact hR.le
    have hdist_lr :
        pointChargeDistanceInMeters setup R
            .left .leftEnd .right .rightEnd =
          R +
            lengthInMeters
              (setup.withinDipoleSeparation .right) := by
      simp [pointChargeDistanceInMeters, chargePositionInMeters,
        dipoleCenterInMeters, endpointOffsetInMeters,
        h_figure.identicalWithinDipoleSeparations]
      rw [show
        -lengthInMeters (setup.withinDipoleSeparation .right) / 2 -
            (R +
              lengthInMeters
                (setup.withinDipoleSeparation .right) / 2) =
          -(R +
            lengthInMeters
              (setup.withinDipoleSeparation .right)) by ring]
      rw [abs_neg, abs_of_pos hplus]
    have hdist_rl :
        pointChargeDistanceInMeters setup R
            .left .rightEnd .right .leftEnd =
          R -
            lengthInMeters
              (setup.withinDipoleSeparation .right) := by
      simp [pointChargeDistanceInMeters, chargePositionInMeters,
        dipoleCenterInMeters, endpointOffsetInMeters,
        h_figure.identicalWithinDipoleSeparations]
      rw [show
        lengthInMeters (setup.withinDipoleSeparation .right) / 2 -
            (R +
              -lengthInMeters
                (setup.withinDipoleSeparation .right) / 2) =
          -(R -
            lengthInMeters
              (setup.withinDipoleSeparation .right)) by ring]
      rw [abs_neg, abs_of_pos hminus]
    have hdist_rr :
        pointChargeDistanceInMeters setup R
            .left .rightEnd .right .rightEnd = R := by
      simp [pointChargeDistanceInMeters, chargePositionInMeters,
        dipoleCenterInMeters, endpointOffsetInMeters,
        h_figure.identicalWithinDipoleSeparations]
      exact hR.le
    rw [h_laws.interactionProfileFromPairwiseCoulombLaw R]
    · unfold crossDipoleCoulombEnergyInJoules
      simp [h_univ_end, signedChargeInCoulombs,
        h_figure.positiveChargesOnLeft,
        h_figure.negativeChargesOnRight, chargeSignFactor,
        h_figure.identicalChargeMagnitudes,
        hdist_ll, hdist_lr, hdist_rl, hdist_rr]
      field_simp [ne_of_gt hR, ne_of_gt hplus, ne_of_gt hminus, hquad]
      ring
    · intro dipole
      cases dipole with
      | left =>
          simpa [h_figure.identicalWithinDipoleSeparations] using hRd
      | right => exact hRd
  have h_inv :
      Filter.Tendsto (fun R : ℝ => R⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h_vanishing_term :
      Filter.Tendsto
        (fun R : ℝ =>
          lengthInMeters
              (setup.withinDipoleSeparation .right) ^ 2 *
            (R⁻¹) ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (h_inv.pow 2)
  have h_denominator :
      Filter.Tendsto
        (fun R : ℝ =>
          1 -
            lengthInMeters
                (setup.withinDipoleSeparation .right) ^ 2 / R ^ 2)
        Filter.atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      tendsto_const_nhds.sub h_vanishing_term
  let coefficient : ℝ :=
    -2 * setup.electromagneticSystem.coulombConstant *
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .right) ^ 2 *
      lengthInMeters (setup.withinDipoleSeparation .right) ^ 2
  have h_constant :
      Filter.Tendsto (fun _ : ℝ => coefficient)
        Filter.atTop (nhds coefficient) :=
    tendsto_const_nhds
  have h_rational_limit :
      Filter.Tendsto
        ((fun _ : ℝ => coefficient) / fun R : ℝ =>
          1 -
            lengthInMeters
                (setup.withinDipoleSeparation .right) ^ 2 / R ^ 2)
        Filter.atTop (nhds coefficient) := by
    simpa using h_constant.div h_denominator (by norm_num)
  have h_profile' :
      (fun R : ℝ =>
          R ^ 3 *
            setup.interactionPotentialEnergyInJoulesAtCenterSeparation R) =ᶠ[
        Filter.atTop]
        ((fun _ : ℝ => coefficient) / fun R : ℝ =>
          1 -
            lengthInMeters
                (setup.withinDipoleSeparation .right) ^ 2 / R ^ 2) := by
    filter_upwards [h_profile] with R hR
    simpa [coefficient] using hR
  have h_coefficient :
      setup.farFieldInteractionCoefficientInJouleMeterCubed =
        coefficient :=
    tendsto_nhds_unique_of_eventuallyEq
      h_laws.farFieldCoefficientFromAsymptoticLimit
      h_rational_limit h_profile'
  rw [h_coefficient]
  dsimp [coefficient]
  have h_permittivity :
      vacuumPermittivityInFaradsPerMeter
          setup.vacuumPermittivity ≠ 0 :=
    ne_of_gt h_physical.vacuumPermittivityPositive
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp [Electromagnetism.EMSystem.coulombConstant,
    h_laws.permittivityMatchesPhyslibSystem,
    h_figure.identicalDipoleMomentMagnitudes,
    h_laws.dipoleMomentIsChargeTimesSeparation]
  field_simp

/-!
For `r ≫ d`, the far-field electric potential energy is the attractive
inverse-cube dipole interaction plus the two internal binding energies.  This
is the formula printed as answer D.

Blueprint: `thm:physics:phyx_mini_0522:target`.
-/
theorem collinear_identical_dipoles_far_field_energy
    (setup : CollinearDipolePairSetup)
    (dimensionlessTolerance : ℝ)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalDipoleParameters setup)
    (h_far_field : IsFarFieldRegime setup dimensionlessTolerance)
    (h_laws : SatisfiesCoulombDipoleLaws setup) :
    energyInJoules setup.farFieldPotentialEnergy =
      -2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters setup.centerSeparation ^ 3) -
        2 * dipoleMomentMagnitudeInCoulombMeters
          (setup.dipoleMomentMagnitude .left) ^ 2 /
          (4 * Real.pi *
            vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity *
            lengthInMeters (setup.withinDipoleSeparation .left) ^ 3) := by
  rw [h_laws.farFieldEnergyAssembly,
    internalPotentialEnergy_formula setup h_figure h_physical h_laws,
    farFieldInteractionCoefficient_formula setup h_figure h_physical h_laws]
  have h_center : lengthInMeters setup.centerSeparation ≠ 0 :=
    ne_of_gt h_physical.centerSeparationPositive
  have h_permittivity :
      vacuumPermittivityInFaradsPerMeter setup.vacuumPermittivity ≠ 0 :=
    ne_of_gt h_physical.vacuumPermittivityPositive
  have h_pi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- The displayed formula established above is answer choice D. -/
theorem recorded_answer_choice_D
    (setup : CollinearDipolePairSetup)
    (dimensionlessTolerance : ℝ)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalDipoleParameters setup)
    (h_far_field : IsFarFieldRegime setup dimensionlessTolerance)
    (h_laws : SatisfiesCoulombDipoleLaws setup) :
    IsCorrectAnswer setup .D := by
  simpa [IsCorrectAnswer, displayedAnswerEnergyInJoules] using
    collinear_identical_dipoles_far_field_energy setup dimensionlessTolerance
      h_figure h_physical h_far_field h_laws

end PhyXMiniProblems.ProblemPhyXMini0522
