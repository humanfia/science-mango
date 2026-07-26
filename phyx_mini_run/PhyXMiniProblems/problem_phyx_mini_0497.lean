import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0497

open Dimension

/-!
# Recoil of a gold-197 nucleus after alpha-particle scattering

An alpha particle approaches a stationary gold-197 nucleus horizontally at
`1.50 * 10^7 m/s`.  It leaves at `1.49 * 10^7 m/s`, at the `49 degree` angle
shown in the primary figure.  Conservation of planar linear momentum then
determines the recoil velocity of the gold nucleus.

Masses and planar velocities are unit-independent Physlib quantities.  Real
numbers occur only as named-unit readouts, dimensionless angles and mass
numbers, and displayed answer values.

Assumption/target boundary:

* `MatchesProblemAndPrimaryFigure` contains the measured speeds, the displayed
  angle, the initially stationary target, and qualitative image evidence.
* `SatisfiesMassNumberApproximation` records the standard mass-number model
  `m_alpha : m_Au = 4 : 197`.
* `SatisfiesScatteringGeometry` converts the measured speed and angle into
  signed planar components.
* `SatisfiesMomentumConservation` is the governing two-body momentum law.
* There are no previous-part results.  Neither the recoil-speed formula nor
  agreement with answer C occurs in any assumption.
-/

/-! ## Dimensionful masses, planar velocities, and readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The horizontal and vertical axes in the scattering plane. -/
inductive PlanarAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- A signed two-dimensional physical velocity with dimension length per time. -/
abbrev PlanarVelocity : Type :=
  Dimensionful
    (WithDim (L𝓭 * T𝓭⁻¹) (EuclideanSpace ℝ PlanarAxis))

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a planar velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocity) : EuclideanSpace ℝ PlanarAxis :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The Euclidean speed readout in metres per SI second. -/
def speedInMetersPerSecond (velocity : PlanarVelocity) : ℝ :=
  ‖velocityReadout LengthUnit.meters TimeUnit.seconds velocity‖

/-- Convert degrees to the radian argument used by `Real.sin` and `Real.cos`. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Particle identities and primary-figure evidence -/

/-- The two physical bodies distinguished in the scattering diagram. -/
inductive FigureObject where
  | alphaParticle
  | gold197Nucleus
  deriving DecidableEq, Repr

/-- Text and numerical labels visible in the primary image. -/
inductive FigureLabel where
  | alphaSymbol
  | gold197Symbol
  | scatteringAngle49Degrees
  deriving DecidableEq, Repr

/-- The three velocity arrows relevant to momentum accounting. -/
inductive VelocityArrow where
  | incomingAlpha
  | scatteredAlpha
  | recoilingGold
  deriving DecidableEq, Repr

/-- Qualitative facts that may be read directly from the supplied diagram. -/
structure AlphaGoldScatteringFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  showsVelocityArrow : VelocityArrow → Bool
  showsPositiveChargeSigns : FigureObject → Bool
  incomingAlphaPointsRight : Bool
  scatteredAlphaIsAboveHorizontal : Bool
  goldRecoilIsBelowHorizontal : Bool
  displayedScatteringAngleDegrees : ℝ

/-!
All physical quantities in the two-body event.  The gold recoil velocity is
an unconstrained dimensionful vector here; its requested magnitude is not a
field of the setup.
-/
structure AlphaGoldScatteringSetup where
  alphaMass : MassQuantity
  goldMass : MassQuantity
  incomingAlphaVelocity : PlanarVelocity
  initialGoldVelocity : PlanarVelocity
  scatteredAlphaVelocity : PlanarVelocity
  goldRecoilVelocity : PlanarVelocity
  scatteringAngleDegrees : ℝ
  figure : AlphaGoldScatteringFigure

/-- The incident alpha speed stated in the problem, in metres per second. -/
def incomingAlphaSpeedDatum : ℝ :=
  (3 / 2 : ℝ) * 10 ^ 7

/-- The scattered alpha speed stated in the problem, in metres per second. -/
def scatteredAlphaSpeedDatum : ℝ :=
  (149 / 100 : ℝ) * 10 ^ 7

/-- The alpha-particle scattering angle shown in the figure, in degrees. -/
def scatteringAngleDegreesDatum : ℝ := 49

/-!
Numerical source data, the stationary-target boundary condition, and primary
image evidence.  No field constrains the gold recoil speed.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : AlphaGoldScatteringSetup) : Prop where
  incomingAlphaSpeed :
    speedInMetersPerSecond setup.incomingAlphaVelocity =
      incomingAlphaSpeedDatum
  scatteredAlphaSpeed :
    speedInMetersPerSecond setup.scatteredAlphaVelocity =
      scatteredAlphaSpeedDatum
  scatteringAngle :
    setup.scatteringAngleDegrees = scatteringAngleDegreesDatum
  goldNucleusInitiallyAtRest :
    velocityReadout LengthUnit.meters TimeUnit.seconds
      setup.initialGoldVelocity = 0
  figureAngleAgrees :
    setup.figure.displayedScatteringAngleDegrees =
      setup.scatteringAngleDegrees
  figureShowsAlpha : setup.figure.showsObject .alphaParticle = true
  figureShowsGold197 : setup.figure.showsObject .gold197Nucleus = true
  figureShowsAlphaLabel : setup.figure.showsLabel .alphaSymbol = true
  figureShowsGold197Label : setup.figure.showsLabel .gold197Symbol = true
  figureShowsAngleLabel :
    setup.figure.showsLabel .scatteringAngle49Degrees = true
  figureShowsIncomingArrow :
    setup.figure.showsVelocityArrow .incomingAlpha = true
  figureShowsScatteredArrow :
    setup.figure.showsVelocityArrow .scatteredAlpha = true
  figureShowsRecoilArrow :
    setup.figure.showsVelocityArrow .recoilingGold = true
  figureShowsPositiveAlpha :
    setup.figure.showsPositiveChargeSigns .alphaParticle = true
  figureShowsPositiveGold :
    setup.figure.showsPositiveChargeSigns .gold197Nucleus = true
  figureIncomingPointsRight : setup.figure.incomingAlphaPointsRight = true
  figureScatteredAbove :
    setup.figure.scatteredAlphaIsAboveHorizontal = true
  figureRecoilBelow : setup.figure.goldRecoilIsBelowHorizontal = true

/-! ## Physical model and governing laws -/

/-!
The usual nuclear mass-number approximation: the alpha particle is assigned
mass number `4` and the gold isotope mass number `197`.  Cross multiplication
states the same unit-independent mass ratio without dividing by a mass.
-/
structure SatisfiesMassNumberApproximation
    (setup : AlphaGoldScatteringSetup) : Prop where
  alphaToGoldMassRatio :
    ∀ massUnit : MassUnit,
      197 * massReadout massUnit setup.alphaMass =
        4 * massReadout massUnit setup.goldMass
  alphaMassPositive :
    0 < massReadout MassUnit.kilograms setup.alphaMass
  goldMassPositive :
    0 < massReadout MassUnit.kilograms setup.goldMass

/-!
Component form of the geometry shown in the image.  The incident alpha defines
the positive horizontal axis, and the scattered alpha lies `theta` above it.
This contains no component or magnitude of the gold recoil velocity.
-/
structure SatisfiesScatteringGeometry
    (setup : AlphaGoldScatteringSetup) : Prop where
  incomingHorizontalComponent :
    velocityReadout LengthUnit.meters TimeUnit.seconds
        setup.incomingAlphaVelocity .horizontal =
      speedInMetersPerSecond setup.incomingAlphaVelocity
  incomingVerticalComponent :
    velocityReadout LengthUnit.meters TimeUnit.seconds
        setup.incomingAlphaVelocity .vertical = 0
  scatteredHorizontalComponent :
    velocityReadout LengthUnit.meters TimeUnit.seconds
        setup.scatteredAlphaVelocity .horizontal =
      speedInMetersPerSecond setup.scatteredAlphaVelocity *
        Real.cos (degreesToRadians setup.scatteringAngleDegrees)
  scatteredVerticalComponent :
    velocityReadout LengthUnit.meters TimeUnit.seconds
        setup.scatteredAlphaVelocity .vertical =
      speedInMetersPerSecond setup.scatteredAlphaVelocity *
        Real.sin (degreesToRadians setup.scatteringAngleDegrees)

/-!
Two-dimensional conservation of linear momentum for the isolated alpha--gold
interaction.  It is stated for every coherent mass and velocity readout.  In
particular, it determines the recoil vector but does not assume its answer
value.
-/
structure SatisfiesMomentumConservation
    (setup : AlphaGoldScatteringSetup) : Prop where
  momentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.alphaMass •
            velocityReadout lengthUnit timeUnit
              setup.incomingAlphaVelocity +
          massReadout massUnit setup.goldMass •
            velocityReadout lengthUnit timeUnit setup.initialGoldVelocity =
        massReadout massUnit setup.alphaMass •
            velocityReadout lengthUnit timeUnit
              setup.scatteredAlphaVelocity +
          massReadout massUnit setup.goldMass •
            velocityReadout lengthUnit timeUnit setup.goldRecoilVelocity

/-! ## Derived recoil speed and displayed answer -/

/-!
The exact recoil-speed formula obtained by taking the Euclidean norm of the
momentum balance and using the included angle between the two alpha velocities.
-/
lemma goldRecoilSpeed_exact
    (setup : AlphaGoldScatteringSetup)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_massModel : SatisfiesMassNumberApproximation setup)
    (_geometry : SatisfiesScatteringGeometry setup)
    (_momentum : SatisfiesMomentumConservation setup) :
    speedInMetersPerSecond setup.goldRecoilVelocity =
      (4 / 197 : ℝ) * Real.sqrt
        (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
          2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
            Real.cos (degreesToRadians scatteringAngleDegreesDatum)) := by
  have hmass :=
    _massModel.alphaToGoldMassRatio MassUnit.kilograms
  have hma :
      massReadout MassUnit.kilograms setup.alphaMass =
        (4 / 197 : ℝ) * massReadout MassUnit.kilograms setup.goldMass := by
    linarith only [hmass]
  have hmom :=
    _momentum.momentumBalance MassUnit.kilograms
      LengthUnit.meters TimeUnit.seconds
  rw [_data.goldNucleusInitiallyAtRest] at hmom
  simp only [smul_zero, add_zero] at hmom
  have hmom_x := congrArg (fun v => v .horizontal) hmom
  have hmom_y := congrArg (fun v => v .vertical) hmom
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hmom_x hmom_y
  rw [_geometry.incomingHorizontalComponent,
    _geometry.scatteredHorizontalComponent, _data.incomingAlphaSpeed,
    _data.scatteredAlphaSpeed, _data.scatteringAngle] at hmom_x
  rw [_geometry.incomingVerticalComponent,
    _geometry.scatteredVerticalComponent, _data.scatteredAlphaSpeed,
    _data.scatteringAngle] at hmom_y
  rw [hma] at hmom_x hmom_y
  have hx :
      velocityReadout LengthUnit.meters TimeUnit.seconds
          setup.goldRecoilVelocity .horizontal =
        (4 / 197 : ℝ) *
          (incomingAlphaSpeedDatum -
            scatteredAlphaSpeedDatum *
              Real.cos (degreesToRadians scatteringAngleDegreesDatum)) := by
    nlinarith only [hmom_x, _massModel.goldMassPositive]
  have hy :
      velocityReadout LengthUnit.meters TimeUnit.seconds
          setup.goldRecoilVelocity .vertical =
        -(4 / 197 : ℝ) *
          (scatteredAlphaSpeedDatum *
            Real.sin (degreesToRadians scatteringAngleDegreesDatum)) := by
    nlinarith only [hmom_y, _massModel.goldMassPositive]
  have hnormsq :
      speedInMetersPerSecond setup.goldRecoilVelocity ^ 2 =
        velocityReadout LengthUnit.meters TimeUnit.seconds
              setup.goldRecoilVelocity .horizontal ^ 2 +
          velocityReadout LengthUnit.meters TimeUnit.seconds
              setup.goldRecoilVelocity .vertical ^ 2 := by
    rw [speedInMetersPerSecond, EuclideanSpace.real_norm_sq_eq]
    rw [show Finset.univ = {.horizontal, .vertical} by decide]
    simp
  rw [hx, hy] at hnormsq
  have htrig :=
    Real.sin_sq_add_cos_sq (degreesToRadians scatteringAngleDegreesDatum)
  have hsq :
      speedInMetersPerSecond setup.goldRecoilVelocity ^ 2 =
        (4 / 197 : ℝ) ^ 2 *
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos (degreesToRadians scatteringAngleDegreesDatum)) := by
    nlinarith only [hnormsq, htrig]
  have hradicand :
      0 ≤ incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
        2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
          Real.cos (degreesToRadians scatteringAngleDegreesDatum) := by
    nlinarith only [htrig,
      sq_nonneg
        (incomingAlphaSpeedDatum -
          scatteredAlphaSpeedDatum *
            Real.cos (degreesToRadians scatteringAngleDegreesDatum)),
      sq_nonneg
        (scatteredAlphaSpeedDatum *
          Real.sin (degreesToRadians scatteringAngleDegreesDatum))]
  have hrhs_sq :
      ((4 / 197 : ℝ) * Real.sqrt
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos (degreesToRadians scatteringAngleDegreesDatum))) ^ 2 =
        (4 / 197 : ℝ) ^ 2 *
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos (degreesToRadians scatteringAngleDegreesDatum)) := by
    rw [mul_pow, Real.sq_sqrt hradicand]
  have hspeed_nonneg :
      0 ≤ speedInMetersPerSecond setup.goldRecoilVelocity :=
    norm_nonneg _
  have hrhs_nonneg :
      0 ≤ (4 / 197 : ℝ) * Real.sqrt
        (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
          2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
            Real.cos (degreesToRadians scatteringAngleDegreesDatum)) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  nlinarith only [hsq, hrhs_sq, hspeed_nonneg, hrhs_nonneg]

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The recoil speed displayed beside each answer label, in metres per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 408 * 10 ^ 3
  | .B => 126 * 10 ^ 3
  | .C => 252 * 10 ^ 3
  | .D => 504 * 10 ^ 3

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a speed displayed to three significant figures.  At the scale
of answer C, half a unit in the last displayed digit is `500 m/s`.
-/
def MatchesAnswerChoice
    (recoilVelocity : PlanarVelocity) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond recoilVelocity -
      choice.speedInMetersPerSecond| ≤ 500

/-!
Momentum conservation with the `4 : 197` mass-number approximation gives the
gold recoil formula above, which agrees to the displayed precision with
recorded answer C, `2.52 * 10^5 m/s`.

Blueprint: `thm:physics:phyx_mini_0497:target`.
-/
theorem problem_phyx_mini_0497
    (setup : AlphaGoldScatteringSetup)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_massModel : SatisfiesMassNumberApproximation setup)
    (_geometry : SatisfiesScatteringGeometry setup)
    (_momentum : SatisfiesMomentumConservation setup) :
    speedInMetersPerSecond setup.goldRecoilVelocity =
        (4 / 197 : ℝ) * Real.sqrt
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos (degreesToRadians scatteringAngleDegreesDatum)) ∧
      MatchesAnswerChoice setup.goldRecoilVelocity recordedAnswerChoice := by
  have hexact :=
    goldRecoilSpeed_exact setup _data _massModel _geometry _momentum
  refine ⟨hexact, ?_⟩
  rw [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.speedInMetersPerSecond, hexact]
  have hpi_lower : (3.14 : ℝ) < Real.pi := by
    have hb := Real.cos_bound (x := (157 / 3200 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 157 / 3200)] at hb
    rw [abs_le] at hb
    norm_num at hb
    have hc0 :
        (9987961 / 10000000 : ℝ) ≤ Real.cos (157 / 3200) := by
      nlinarith only [hb.1]
    have h1 := Real.cos_two_mul (157 / 3200 : ℝ)
    norm_num at h1
    have hc1 :
        (9951872 / 10000000 : ℝ) ≤ Real.cos (157 / 1600) := by
      rw [h1]
      nlinarith only [hc0]
    have h2 := Real.cos_two_mul (157 / 1600 : ℝ)
    norm_num at h2
    have hc2 :
        (9807951 / 10000000 : ℝ) ≤ Real.cos (157 / 800) := by
      rw [h2]
      nlinarith only [hc1]
    have h3 := Real.cos_two_mul (157 / 800 : ℝ)
    norm_num at h3
    have hc3 :
        (923918 / 1000000 : ℝ) ≤ Real.cos (157 / 400) := by
      rw [h3]
      nlinarith only [hc2]
    have h4 := Real.cos_two_mul (157 / 400 : ℝ)
    norm_num at h4
    have hc4 :
        (707248 / 1000000 : ℝ) ≤ Real.cos (157 / 200) := by
      rw [h4]
      nlinarith only [hc3]
    have h5 := Real.cos_two_mul (157 / 200 : ℝ)
    norm_num at h5
    have hcos : 0 < Real.cos (157 / 100 : ℝ) := by
      rw [h5]
      nlinarith only [hc4]
    by_contra hpi
    have hhalf : Real.pi / 2 ≤ (157 / 100 : ℝ) := by
      push Not at hpi
      linarith only [hpi]
    have hnonpos : Real.cos (157 / 100 : ℝ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hhalf
        (by linarith only [Real.two_le_pi])
    linarith only [hcos, hnonpos]
  have hpi_upper : Real.pi < (3.15 : ℝ) := by
    have hb := Real.cos_bound (x := (63 / 1280 : ℝ)) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 63 / 1280)] at hb
    rw [abs_le] at hb
    norm_num at hb
    have hc0 :
        Real.cos (63 / 1280) ≤ (99879 / 100000 : ℝ) := by
      nlinarith only [hb.2]
    have h1 := Real.cos_two_mul (63 / 1280 : ℝ)
    norm_num at h1
    have hc1 :
        Real.cos (63 / 640) ≤ (995163 / 1000000 : ℝ) := by
      rw [h1]
      nlinarith only [hc0,
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (x := (63 / 1280 : ℝ))
          (by linarith only [Real.two_le_pi])
          (by linarith only [Real.two_le_pi])]
    have h2 := Real.cos_two_mul (63 / 640 : ℝ)
    norm_num at h2
    have hc2 :
        Real.cos (63 / 320) ≤ (9807 / 10000 : ℝ) := by
      rw [h2]
      nlinarith only [hc1,
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (x := (63 / 640 : ℝ))
          (by linarith only [Real.two_le_pi])
          (by linarith only [Real.two_le_pi])]
    have h3 := Real.cos_two_mul (63 / 320 : ℝ)
    norm_num at h3
    have hc3 :
        Real.cos (63 / 160) ≤ (92355 / 100000 : ℝ) := by
      rw [h3]
      nlinarith only [hc2,
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (x := (63 / 320 : ℝ))
          (by linarith only [Real.two_le_pi])
          (by linarith only [Real.two_le_pi])]
    have h4 := Real.cos_two_mul (63 / 160 : ℝ)
    norm_num at h4
    have hc4 :
        Real.cos (63 / 80) ≤ (706 / 1000 : ℝ) := by
      rw [h4]
      nlinarith only [hc3,
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (x := (63 / 160 : ℝ))
          (by linarith only [Real.two_le_pi])
          (by linarith only [Real.two_le_pi])]
    have h5 := Real.cos_two_mul (63 / 80 : ℝ)
    norm_num at h5
    have hcos : Real.cos (63 / 40 : ℝ) < 0 := by
      rw [h5]
      nlinarith only [hc4,
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (x := (63 / 80 : ℝ))
          (by linarith only [Real.two_le_pi])
          (by linarith only [Real.two_le_pi])]
    by_contra hpi
    have hhalf : (63 / 40 : ℝ) ≤ Real.pi / 2 := by
      push Not at hpi
      linarith only [hpi]
    have hnonneg : 0 ≤ Real.cos (63 / 40 : ℝ) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith only [Real.two_le_pi]) hhalf
    linarith only [hcos, hnonneg]
  have hdpos : 0 ≤ Real.pi / 45 := by positivity
  have hdlo : (157 / 2250 : ℝ) ≤ Real.pi / 45 := by
    linarith only [hpi_lower]
  have hdhi : Real.pi / 45 ≤ (7 / 100 : ℝ) := by
    linarith only [hpi_upper]
  have hd4 : (Real.pi / 45) ^ 4 ≤ (7 / 100 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hdpos hdhi 4
  have hd2lo :
      (157 / 2250 : ℝ) ^ 2 ≤ (Real.pi / 45) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hdlo 2
  have hd2hi : (Real.pi / 45) ^ 2 ≤ (7 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hdpos hdhi 2
  have hd3lo :
      (157 / 2250 : ℝ) ^ 3 ≤ (Real.pi / 45) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hdlo 3
  have hd3hi : (Real.pi / 45) ^ 3 ≤ (7 / 100 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hdpos hdhi 3
  have hcos_delta := Real.cos_bound (x := Real.pi / 45) (by
    rw [abs_of_nonneg hdpos]
    linarith only [hdhi])
  rw [abs_of_nonneg hdpos, abs_le] at hcos_delta
  have hsin_delta := Real.sin_bound (x := Real.pi / 45) (by
    rw [abs_of_nonneg hdpos]
    linarith only [hdhi])
  rw [abs_of_nonneg hdpos, abs_le] at hsin_delta
  have hcos_delta_lower :
      (9975 / 10000 : ℝ) ≤ Real.cos (Real.pi / 45) := by
    nlinarith only [hcos_delta.1, hd2hi, hd4]
  have hcos_delta_upper :
      Real.cos (Real.pi / 45) ≤ (9976 / 10000 : ℝ) := by
    nlinarith only [hcos_delta.2, hd2lo, hd4]
  have hsin_delta_lower :
      (697 / 10000 : ℝ) ≤ Real.sin (Real.pi / 45) := by
    nlinarith only [hsin_delta.1, hdlo, hd3hi, hd4]
  have hsin_delta_upper :
      Real.sin (Real.pi / 45) ≤ (7 / 100 : ℝ) := by
    nlinarith only [hsin_delta.2, hdhi, hd3lo, hd4]
  have hsqrt2 : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt2half_sq :
      (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    nlinarith only [hsqrt2]
  have hsqrt2half_nonneg : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hsqrt2half_lower :
      (7071 / 10000 : ℝ) ≤ Real.sqrt 2 / 2 := by
    nlinarith only [hsqrt2half_sq, hsqrt2half_nonneg]
  have hsqrt2half_upper :
      Real.sqrt 2 / 2 ≤ (7072 / 10000 : ℝ) := by
    nlinarith only [hsqrt2half_sq, hsqrt2half_nonneg]
  have hdelta_diff_lower :
      (9975 / 10000 - 7 / 100 : ℝ) ≤
        Real.cos (Real.pi / 45) - Real.sin (Real.pi / 45) := by
    linarith only [hcos_delta_lower, hsin_delta_upper]
  have hdelta_diff_upper :
      Real.cos (Real.pi / 45) - Real.sin (Real.pi / 45) ≤
        (9976 / 10000 - 697 / 10000 : ℝ) := by
    linarith only [hcos_delta_upper, hsin_delta_lower]
  have hdelta_diff_nonneg :
      0 ≤ Real.cos (Real.pi / 45) - Real.sin (Real.pi / 45) := by
    linarith only [hcos_delta_lower, hsin_delta_upper]
  have hproduct_lower :=
    mul_le_mul hsqrt2half_lower hdelta_diff_lower
      (by norm_num) hsqrt2half_nonneg
  have hproduct_upper :=
    mul_le_mul hsqrt2half_upper hdelta_diff_upper
      hdelta_diff_nonneg (by norm_num)
  have hangle :
      degreesToRadians scatteringAngleDegreesDatum =
        Real.pi / 4 + Real.pi / 45 := by
    norm_num [degreesToRadians, scatteringAngleDegreesDatum]
    ring
  have hcos_lower :
      (6541 / 10000 : ℝ) ≤
        Real.cos (degreesToRadians scatteringAngleDegreesDatum) := by
    rw [hangle, Real.cos_add, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    nlinarith only [hproduct_lower]
  have hcos_upper :
      Real.cos (degreesToRadians scatteringAngleDegreesDatum) ≤
        (6567 / 10000 : ℝ) := by
    rw [hangle, Real.cos_add, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    nlinarith only [hproduct_upper]
  have hradicand :
      0 ≤ incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
        2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
          Real.cos (degreesToRadians scatteringAngleDegreesDatum) := by
    norm_num [incomingAlphaSpeedDatum, scatteredAlphaSpeedDatum]
    nlinarith only [hcos_upper]
  have hsquare :
      ((4 / 197 : ℝ) * Real.sqrt
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos
                (degreesToRadians scatteringAngleDegreesDatum))) ^ 2 =
        (4 / 197 : ℝ) ^ 2 *
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos
                (degreesToRadians scatteringAngleDegreesDatum)) := by
    rw [mul_pow, Real.sq_sqrt hradicand]
  have hlower_sq :
      (251500 : ℝ) ^ 2 ≤
        ((4 / 197 : ℝ) * Real.sqrt
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos
                (degreesToRadians scatteringAngleDegreesDatum))) ^ 2 := by
    rw [hsquare]
    norm_num [incomingAlphaSpeedDatum, scatteredAlphaSpeedDatum]
    nlinarith only [hcos_upper]
  have hupper_sq :
      ((4 / 197 : ℝ) * Real.sqrt
          (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
            2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
              Real.cos
                (degreesToRadians scatteringAngleDegreesDatum))) ^ 2 ≤
        (252500 : ℝ) ^ 2 := by
    rw [hsquare]
    norm_num [incomingAlphaSpeedDatum, scatteredAlphaSpeedDatum]
    nlinarith only [hcos_lower]
  have hspeed_nonneg :
      0 ≤ (4 / 197 : ℝ) * Real.sqrt
        (incomingAlphaSpeedDatum ^ 2 + scatteredAlphaSpeedDatum ^ 2 -
          2 * incomingAlphaSpeedDatum * scatteredAlphaSpeedDatum *
            Real.cos (degreesToRadians scatteringAngleDegreesDatum)) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rw [show (252 : ℝ) * 10 ^ 3 = 252000 by norm_num]
  rw [abs_le]
  constructor
  · nlinarith only [hlower_sq, hspeed_nonneg]
  · nlinarith only [hupper_sq, hspeed_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0497
