import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0970

open Dimension MeasureTheory

/-!
# Gyromagnetic ratio of a uniformly charged spherical shell

A thin spherical shell of radius `R`, total mass `M`, and uniformly distributed
charge `Q` rotates rigidly about the positive `z`-axis with angular speed
`omega`.  The shell is decomposed into latitude bands at polar angle `theta`.
For each band, the figure's radius is `r = R sin theta` and the band current is
`dI = omega dq / (2 pi)`.  The mechanical and magnetic contributions are
`dL_z = r^2 omega dm` and `dmu_z = pi r^2 dI`, respectively.

All physical quantities below are unit-independent Physlib `Dimensionful`
values.  Real numbers and Euclidean vectors occur only as coherent-unit
readouts, dimensionless angles and factors, or literal raster data.

Assumption/target split:

* `MatchesUniformRotatingShellScenario` states the thin-shell, uniform surface
  mass/charge, central-origin, and positive-`z` rotation data;
* `MatchesPrimaryFigure` records the labels `O`, `z`, `omega`, `R`, `theta`,
  `r`, `dI`, `Q`, and `M` visible in image `970.png`;
* `SatisfiesLatitudeBandGeometry` and `SatisfiesRigidRotationBandLaws` are the
  governing surface-band geometry, current, angular-momentum, and magnetic-
  moment laws;
* `SatisfiesGyromagneticRelations` records only the two definitions supplied
  in the question, `mu = gamma L` and `gamma = g Q/(2M)`;
* there are no previous-part results; and
* `gamma = Q/(2M)`, equivalently `g = 1` and answer B, occurs only in derived
  lemma/theorem conclusions.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- Three-dimensional Euclidean vectors used for coherent-unit readouts. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- Angular speed has inverse-time dimension; radians are dimensionless. -/
def angularSpeedDimension : Dimension :=
  T𝓭⁻¹

/-- Surface mass density has dimension `mass / length^2`. -/
def surfaceMassDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- Surface charge density has dimension `charge / length^2`. -/
def surfaceChargeDensityDimension : Dimension :=
  C𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- Electric current has dimension `charge / time`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Angular momentum has dimension `mass * length^2 / time`. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Magnetic dipole moment has dimension `charge * length^2 / time`. -/
def magneticMomentDimension : Dimension :=
  C𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A gyromagnetic ratio has dimension `charge / mass`. -/
def gyromagneticRatioDimension : Dimension :=
  C𝓭 * M𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassMagnitude : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed mass assigned to a latitude band per radian of polar angle. -/
abbrev LatitudeBandMassDensity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent position vector. -/
abbrev PositionVector : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A signed, unit-independent electric charge. -/
abbrev ChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- Signed charge assigned to a latitude band per radian of polar angle. -/
abbrev LatitudeBandChargeDensity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedMagnitude : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative uniform surface mass density. -/
abbrev SurfaceMassDensityMagnitude : Type :=
  Dimensionful (WithDim surfaceMassDensityDimension NNReal)

/-- A signed uniform surface charge density. -/
abbrev SurfaceChargeDensityQuantity : Type :=
  Dimensionful (WithDim surfaceChargeDensityDimension ℝ)

/-- A signed electric current carried by a latitude band per radian. -/
abbrev LatitudeBandCurrentDensity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A unit-independent three-vector angular momentum. -/
abbrev AngularMomentumVector : Type :=
  Dimensionful (WithDim angularMomentumDimension SpatialVector)

/-- A unit-independent three-vector magnetic dipole moment. -/
abbrev MagneticMomentVector : Type :=
  Dimensionful (WithDim magneticMomentDimension SpatialVector)

/-- A signed, unit-independent gyromagnetic ratio. -/
abbrev GyromagneticRatioQuantity : Type :=
  Dimensionful (WithDim gyromagneticRatioDimension ℝ)

/-- Read a nonnegative dimensionful scalar in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful scalar in a coherent unit system. -/
def signedReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Read a dimensionful spatial vector in a coherent unit system. -/
def vectorReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d SpatialVector)) : SpatialVector :=
  (quantity units).val

/-- The dimensionless positive-`z` coordinate unit vector. -/
def zHat : SpatialVector :=
  EuclideanSpace.single (2 : Fin 3) 1

/-! ## Physical system, latitude bands, and figure vocabulary -/

/-- The geometric support chosen for the body's mass and charge. -/
inductive ShellGeometryModel where
  | thinSphericalSurface
  | other
  deriving DecidableEq, Repr

/-- The mass distribution on the spherical surface. -/
inductive SurfaceMassDistributionModel where
  | uniform
  | other
  deriving DecidableEq, Repr

/-- The charge distribution on the spherical surface. -/
inductive SurfaceChargeDistributionModel where
  | uniform
  | other
  deriving DecidableEq, Repr

/-- The kinematic motion of the mass and charge distributions. -/
inductive RotationModel where
  | rigidAboutCentralAxis
  | other
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied primary image. -/
inductive FigureLabel where
  | centerO
  | zAxis
  | angularSpeedOmega
  | shellRadiusR
  | polarAngleTheta
  | latitudeRadiusR
  | bandCurrentElementDI
  | totalChargeQ
  | totalMassM
  deriving DecidableEq, Fintype, Repr

/-!
Latitude-band quantities indexed by the dimensionless polar angle `theta`.
Because radians are dimensionless, the per-radian quantities retain the mass,
charge, and current dimensions shown in their types.
-/
structure LatitudeBandProfile where
  ringRadius : ℝ → LengthMagnitude
  massPerPolarRadian : ℝ → LatitudeBandMassDensity
  chargePerPolarRadian : ℝ → LatitudeBandChargeDensity
  currentPerPolarRadian : ℝ → LatitudeBandCurrentDensity

/-- Quantitative and qualitative data transcribed from image `970.png`. -/
structure RotatingShellFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  labelShown : FigureLabel → Bool
  translucentSphereShown : Bool
  verticalAxisShown : Bool
  latitudeBandShown : Bool
  rotationArrowShown : Bool
  bandCurrentArrowShown : Bool
  polarAngleRadians : ℝ
  displayedRadiusRay : LengthMagnitude
  displayedLatitudeRadius : LengthMagnitude
  displayedBandCurrentElement : LatitudeBandCurrentDensity

/-!
The independent parameters and observables of the rotating shell.  In
particular, neither `gyromagneticRatio` nor `gFactor` is defined from a
displayed answer or from `Q/(2M)`.
-/
structure RotatingChargedShellSetup where
  geometryModel : ShellGeometryModel
  massDistribution : SurfaceMassDistributionModel
  chargeDistribution : SurfaceChargeDistributionModel
  rotationModel : RotationModel
  center : PositionVector
  rotationAxis : SpatialVector
  totalMass : MassMagnitude
  totalCharge : ChargeQuantity
  shellRadius : LengthMagnitude
  angularSpeed : AngularSpeedMagnitude
  surfaceMassDensity : SurfaceMassDensityMagnitude
  surfaceChargeDensity : SurfaceChargeDensityQuantity
  angularMomentum : AngularMomentumVector
  magneticMoment : MagneticMomentVector
  gyromagneticRatio : GyromagneticRatioQuantity
  gFactor : ℝ
  bands : LatitudeBandProfile
  figure : RotatingShellFigure

/-! ## Scenario, figure evidence, and governing physics -/

/-!
The thin shell, common uniform surface support, origin, and central `z`-axis
rotation stated by the problem.  The density equations are uniform-surface
data; they contain no magnetic moment, angular momentum, gyromagnetic ratio,
or g-factor.
-/
structure MatchesUniformRotatingShellScenario
    (setup : RotatingChargedShellSetup) : Prop where
  geometryIsThinSphericalSurface :
    setup.geometryModel = .thinSphericalSurface
  massIsUniformOnSurface :
    setup.massDistribution = .uniform
  chargeIsUniformOnSurface :
    setup.chargeDistribution = .uniform
  rotationIsRigidAndCentral :
    setup.rotationModel = .rigidAboutCentralAxis
  centerIsOrigin : ∀ units : UnitChoices,
    vectorReadout units setup.center = 0
  axisIsPositiveZ : setup.rotationAxis = zHat
  uniformSurfaceMassDensity : ∀ units : UnitChoices,
    nonnegativeReadout units setup.surfaceMassDensity =
      nonnegativeReadout units setup.totalMass /
        (4 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2)
  uniformSurfaceChargeDensity : ∀ units : UnitChoices,
    signedReadout units setup.surfaceChargeDensity =
      signedReadout units setup.totalCharge /
        (4 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2)

/-- Exact qualitative labels and geometry visible in the `366 x 423` image. -/
structure MatchesPrimaryFigure (setup : RotatingChargedShellSetup) : Prop where
  rasterWidth : setup.figure.rasterWidthPixels = 366
  rasterHeight : setup.figure.rasterHeightPixels = 423
  everyPrintedLabelIsShown : ∀ label,
    setup.figure.labelShown label = true
  translucentSphereVisible : setup.figure.translucentSphereShown = true
  verticalAxisVisible : setup.figure.verticalAxisShown = true
  latitudeBandVisible : setup.figure.latitudeBandShown = true
  angularVelocityArrowVisible : setup.figure.rotationArrowShown = true
  currentDirectionArrowVisible : setup.figure.bandCurrentArrowShown = true
  displayedAngleInPolarRange :
    setup.figure.polarAngleRadians ∈ Set.Icc (0 : ℝ) Real.pi
  displayedRadiusIsShellRadius :
    setup.figure.displayedRadiusRay = setup.shellRadius
  displayedRingRadiusComesFromBandProfile :
    setup.figure.displayedLatitudeRadius =
      setup.bands.ringRadius setup.figure.polarAngleRadians
  displayedDIComesFromBandProfile :
    setup.figure.displayedBandCurrentElement =
      setup.bands.currentPerPolarRadian setup.figure.polarAngleRadians

/-- Strict physical nondegeneracy used to determine `gamma` and `g` uniquely. -/
structure HasNondegenerateShellParameters
    (setup : RotatingChargedShellSetup) : Prop where
  positiveMass : 0 < nonnegativeReadout UnitChoices.SI setup.totalMass
  nonzeroCharge : signedReadout UnitChoices.SI setup.totalCharge ≠ 0
  positiveRadius : 0 < nonnegativeReadout UnitChoices.SI setup.shellRadius
  positiveAngularSpeed :
    0 < nonnegativeReadout UnitChoices.SI setup.angularSpeed

/-!
Spherical latitude-band geometry.  A band between `theta` and
`theta + dtheta` has area per radian `2 pi R^2 sin theta`; multiplying by the
uniform surface densities gives its mass and charge per polar radian.  The
ring radius is `R sin theta`, as shown in the figure.
-/
structure SatisfiesLatitudeBandGeometry
    (setup : RotatingChargedShellSetup) : Prop where
  latitudeRingRadius : ∀ (units : UnitChoices) (theta : ℝ),
    theta ∈ Set.Icc (0 : ℝ) Real.pi →
      nonnegativeReadout units (setup.bands.ringRadius theta) =
        nonnegativeReadout units setup.shellRadius * Real.sin theta
  latitudeBandMass : ∀ (units : UnitChoices) (theta : ℝ),
    theta ∈ Set.Icc (0 : ℝ) Real.pi →
      signedReadout units (setup.bands.massPerPolarRadian theta) =
        nonnegativeReadout units setup.surfaceMassDensity *
          (2 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2 *
            Real.sin theta)
  latitudeBandCharge : ∀ (units : UnitChoices) (theta : ℝ),
    theta ∈ Set.Icc (0 : ℝ) Real.pi →
      signedReadout units (setup.bands.chargePerPolarRadian theta) =
        signedReadout units setup.surfaceChargeDensity *
          (2 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2 *
            Real.sin theta)

/-!
The governing rigid-rotation and current-loop laws.  Each latitude band's
current is its charge per radian times the rotation frequency
`omega/(2 pi)`.  Total angular momentum and magnetic moment are obtained by
integrating `r^2 omega dm` and `pi r^2 dI` along the positive rotation axis.
No gyromagnetic ratio or answer choice occurs in these laws.
-/
structure SatisfiesRigidRotationBandLaws
    (setup : RotatingChargedShellSetup) : Prop where
  rotatingBandCurrent : ∀ (units : UnitChoices) (theta : ℝ),
    theta ∈ Set.Icc (0 : ℝ) Real.pi →
      signedReadout units (setup.bands.currentPerPolarRadian theta) =
        signedReadout units (setup.bands.chargePerPolarRadian theta) *
          nonnegativeReadout units setup.angularSpeed / (2 * Real.pi)
  totalAngularMomentumFromBands : ∀ units : UnitChoices,
    vectorReadout units setup.angularMomentum =
      (∫ theta in Set.Icc (0 : ℝ) Real.pi,
        signedReadout units (setup.bands.massPerPolarRadian theta) *
          nonnegativeReadout units setup.angularSpeed *
          nonnegativeReadout units (setup.bands.ringRadius theta) ^ 2) •
        setup.rotationAxis
  totalMagneticMomentFromBands : ∀ units : UnitChoices,
    vectorReadout units setup.magneticMoment =
      (∫ theta in Set.Icc (0 : ℝ) Real.pi,
        Real.pi * nonnegativeReadout units (setup.bands.ringRadius theta) ^ 2 *
          signedReadout units (setup.bands.currentPerPolarRadian theta)) •
        setup.rotationAxis

/-!
The two proportionalities explicitly supplied in the question.  They relate
independent observables and do not set either `gamma` or `g` to its requested
value.
-/
structure SatisfiesGyromagneticRelations
    (setup : RotatingChargedShellSetup) : Prop where
  magneticMomentIsGammaTimesAngularMomentum : ∀ units : UnitChoices,
    vectorReadout units setup.magneticMoment =
      signedReadout units setup.gyromagneticRatio •
        vectorReadout units setup.angularMomentum
  gammaIsGTimesChargeOverTwiceMass : ∀ units : UnitChoices,
    signedReadout units setup.gyromagneticRatio =
      setup.gFactor * signedReadout units setup.totalCharge /
        (2 * nonnegativeReadout units setup.totalMass)

/-! ## Derived shell relations -/

/-!
The latitude-band integral of `r^2 omega dm` gives the standard thin-shell
axial angular momentum `(2/3) M R^2 omega`.
-/
lemma uniformSphericalShellAngularMomentum
    (setup : RotatingChargedShellSetup)
    (_scenario : MatchesUniformRotatingShellScenario setup)
    (_physical : HasNondegenerateShellParameters setup)
    (_geometry : SatisfiesLatitudeBandGeometry setup)
    (_laws : SatisfiesRigidRotationBandLaws setup) :
    ∀ units : UnitChoices,
      vectorReadout units setup.angularMomentum =
        ((2 / 3 : ℝ) * nonnegativeReadout units setup.totalMass *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed) • zHat := by
  intro units
  have hr_pos : 0 < nonnegativeReadout units setup.shellRadius := by
    rw [nonnegativeReadout, setup.shellRadius.2 UnitChoices.SI units]
    simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
    exact mul_pos
      (by exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units L𝓭)
      _physical.positiveRadius
  have hr_ne : nonnegativeReadout units setup.shellRadius ≠ 0 :=
    ne_of_gt hr_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsin :
      (∫ theta in Set.Icc (0 : ℝ) Real.pi, Real.sin theta ^ 3) = 4 / 3 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
    norm_num [integral_sin_pow_odd]
  rw [_laws.totalAngularMomentumFromBands units, _scenario.axisIsPositiveZ]
  congr 1
  calc
    (∫ theta in Set.Icc (0 : ℝ) Real.pi,
        signedReadout units (setup.bands.massPerPolarRadian theta) *
          nonnegativeReadout units setup.angularSpeed *
          nonnegativeReadout units (setup.bands.ringRadius theta) ^ 2) =
        ∫ theta in Set.Icc (0 : ℝ) Real.pi,
          (nonnegativeReadout units setup.totalMass /
              (4 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2) *
            (2 * Real.pi * nonnegativeReadout units setup.shellRadius ^ 2 *
              Real.sin theta)) *
            nonnegativeReadout units setup.angularSpeed *
            (nonnegativeReadout units setup.shellRadius * Real.sin theta) ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro theta htheta
      simp only
      rw [_geometry.latitudeBandMass units theta htheta,
        _geometry.latitudeRingRadius units theta htheta,
        _scenario.uniformSurfaceMassDensity units]
    _ = ∫ theta in Set.Icc (0 : ℝ) Real.pi,
        (nonnegativeReadout units setup.totalMass *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed / 2) *
          Real.sin theta ^ 3 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro theta _
      field_simp [hpi_ne, hr_ne]
      <;> ring
    _ = (nonnegativeReadout units setup.totalMass *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed / 2) *
        ∫ theta in Set.Icc (0 : ℝ) Real.pi, Real.sin theta ^ 3 := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 / 3 : ℝ) * nonnegativeReadout units setup.totalMass *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed := by
      rw [hsin]
      ring

/-!
The latitude-band integral of `pi r^2 dI` gives the thin-shell magnetic
moment `(1/3) Q R^2 omega`.
-/
lemma uniformSphericalShellMagneticMoment
    (setup : RotatingChargedShellSetup)
    (_scenario : MatchesUniformRotatingShellScenario setup)
    (_physical : HasNondegenerateShellParameters setup)
    (_geometry : SatisfiesLatitudeBandGeometry setup)
    (_laws : SatisfiesRigidRotationBandLaws setup) :
    ∀ units : UnitChoices,
      vectorReadout units setup.magneticMoment =
        ((1 / 3 : ℝ) * signedReadout units setup.totalCharge *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed) • zHat := by
  intro units
  have hr_pos : 0 < nonnegativeReadout units setup.shellRadius := by
    rw [nonnegativeReadout, setup.shellRadius.2 UnitChoices.SI units]
    simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
    exact mul_pos
      (by exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units L𝓭)
      _physical.positiveRadius
  have hr_ne : nonnegativeReadout units setup.shellRadius ≠ 0 :=
    ne_of_gt hr_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsin :
      (∫ theta in Set.Icc (0 : ℝ) Real.pi, Real.sin theta ^ 3) = 4 / 3 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
    norm_num [integral_sin_pow_odd]
  rw [_laws.totalMagneticMomentFromBands units, _scenario.axisIsPositiveZ]
  congr 1
  calc
    (∫ theta in Set.Icc (0 : ℝ) Real.pi,
        Real.pi *
          nonnegativeReadout units (setup.bands.ringRadius theta) ^ 2 *
          signedReadout units (setup.bands.currentPerPolarRadian theta)) =
        ∫ theta in Set.Icc (0 : ℝ) Real.pi,
          Real.pi *
            (nonnegativeReadout units setup.shellRadius * Real.sin theta) ^ 2 *
            ((signedReadout units setup.totalCharge /
                (4 * Real.pi *
                  nonnegativeReadout units setup.shellRadius ^ 2) *
              (2 * Real.pi *
                nonnegativeReadout units setup.shellRadius ^ 2 *
                Real.sin theta)) *
              nonnegativeReadout units setup.angularSpeed /
              (2 * Real.pi)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro theta htheta
      simp only
      rw [_geometry.latitudeRingRadius units theta htheta,
        _laws.rotatingBandCurrent units theta htheta,
        _geometry.latitudeBandCharge units theta htheta,
        _scenario.uniformSurfaceChargeDensity units]
    _ = ∫ theta in Set.Icc (0 : ℝ) Real.pi,
        (signedReadout units setup.totalCharge *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed / 4) *
          Real.sin theta ^ 3 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro theta _
      field_simp [hpi_ne, hr_ne]
      <;> ring
    _ = (signedReadout units setup.totalCharge *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed / 4) *
        ∫ theta in Set.Icc (0 : ℝ) Real.pi, Real.sin theta ^ 3 := by
      rw [MeasureTheory.integral_const_mul]
    _ = (1 / 3 : ℝ) * signedReadout units setup.totalCharge *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed := by
      rw [hsin]
      ring

/-!
Comparing the two independently derived band integrals gives
`mu = (Q/(2M)) L`.  This is a derived conclusion rather than a premise.
-/
lemma uniformSphericalShellMomentMomentumRelation
    (setup : RotatingChargedShellSetup)
    (_scenario : MatchesUniformRotatingShellScenario setup)
    (_physical : HasNondegenerateShellParameters setup)
    (_geometry : SatisfiesLatitudeBandGeometry setup)
    (_laws : SatisfiesRigidRotationBandLaws setup) :
    ∀ units : UnitChoices,
      vectorReadout units setup.magneticMoment =
        (signedReadout units setup.totalCharge /
          (2 * nonnegativeReadout units setup.totalMass)) •
            vectorReadout units setup.angularMomentum := by
  intro units
  have hm_pos : 0 < nonnegativeReadout units setup.totalMass := by
    rw [nonnegativeReadout, setup.totalMass.2 UnitChoices.SI units]
    simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
    exact mul_pos
      (by exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units M𝓭)
      _physical.positiveMass
  have hm_ne : nonnegativeReadout units setup.totalMass ≠ 0 :=
    ne_of_gt hm_pos
  rw [uniformSphericalShellMagneticMoment setup _scenario _physical _geometry
      _laws units,
    uniformSphericalShellAngularMomentum setup _scenario _physical _geometry
      _laws units,
    smul_smul]
  congr 1
  field_simp [hm_ne]
  <;> ring

/-! ## Displayed choices and current target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Coherent-unit readout of the formula printed beside an answer label. -/
def displayedGyromagneticRatioReadout
    (setup : RotatingChargedShellSetup)
    (choice : AnswerChoice) (units : UnitChoices) : ℝ :=
  match choice with
  | .A =>
      signedReadout units setup.totalCharge /
        nonnegativeReadout units setup.totalMass
  | .B =>
      signedReadout units setup.totalCharge /
        (2 * nonnegativeReadout units setup.totalMass)
  | .C =>
      signedReadout units setup.totalCharge /
        (4 * nonnegativeReadout units setup.totalMass)
  | .D =>
      2 * signedReadout units setup.totalCharge /
        (3 * nonnegativeReadout units setup.totalMass)

/-- Dataset metadata recording answer B; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice :=
  .B

/-- Agreement of an independent physical `gamma` with a displayed formula. -/
def MatchesDisplayedGyromagneticRatio
    (setup : RotatingChargedShellSetup) (choice : AnswerChoice) : Prop :=
  ∀ units : UnitChoices,
    signedReadout units setup.gyromagneticRatio =
      displayedGyromagneticRatioReadout setup choice units

/-!
The two latitude-band integrals yield
`L = (2/3) M R^2 omega` and `mu = (1/3) Q R^2 omega`.  Hence the defining
relation `mu = gamma L` forces `gamma = Q/(2M)`.  Comparison with
`gamma = g Q/(2M)` gives `g = 1`, so B is the unique matching displayed
choice.

Blueprint: `thm:physics:phyx_mini_0970:target`.
-/
theorem gyromagneticRatioOfUniformSphericalShell
    (setup : RotatingChargedShellSetup)
    (_scenario : MatchesUniformRotatingShellScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasNondegenerateShellParameters setup)
    (_geometry : SatisfiesLatitudeBandGeometry setup)
    (_laws : SatisfiesRigidRotationBandLaws setup)
    (_gyromagnetic : SatisfiesGyromagneticRelations setup) :
    (∀ units : UnitChoices,
      signedReadout units setup.gyromagneticRatio =
        signedReadout units setup.totalCharge /
          (2 * nonnegativeReadout units setup.totalMass)) ∧
      setup.gFactor = 1 ∧
      MatchesDisplayedGyromagneticRatio setup .B ∧
      ∀ choice : AnswerChoice,
        MatchesDisplayedGyromagneticRatio setup choice → choice = .B := by
  have hgamma : ∀ units : UnitChoices,
      signedReadout units setup.gyromagneticRatio =
        signedReadout units setup.totalCharge /
          (2 * nonnegativeReadout units setup.totalMass) := by
    intro units
    have hm_pos : 0 < nonnegativeReadout units setup.totalMass := by
      rw [nonnegativeReadout, setup.totalMass.2 UnitChoices.SI units]
      simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
      exact mul_pos
        (by exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units M𝓭)
        _physical.positiveMass
    have hr_pos : 0 < nonnegativeReadout units setup.shellRadius := by
      rw [nonnegativeReadout, setup.shellRadius.2 UnitChoices.SI units]
      simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
      exact mul_pos
        (by exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units L𝓭)
        _physical.positiveRadius
    have hw_pos : 0 < nonnegativeReadout units setup.angularSpeed := by
      rw [nonnegativeReadout, setup.angularSpeed.2 UnitChoices.SI units]
      simp only [WithDim.smul_val, NNReal.smul_def, NNReal.coe_mul]
      exact mul_pos
        (by
          exact_mod_cast UnitChoices.dimScale_pos UnitChoices.SI units
            angularSpeedDimension)
        _physical.positiveAngularSpeed
    have hLcoeff_pos :
        0 < (2 / 3 : ℝ) * nonnegativeReadout units setup.totalMass *
          nonnegativeReadout units setup.shellRadius ^ 2 *
          nonnegativeReadout units setup.angularSpeed := by
      positivity
    have hv :
        signedReadout units setup.gyromagneticRatio •
            vectorReadout units setup.angularMomentum =
          (signedReadout units setup.totalCharge /
            (2 * nonnegativeReadout units setup.totalMass)) •
              vectorReadout units setup.angularMomentum :=
      (_gyromagnetic.magneticMomentIsGammaTimesAngularMomentum units).symm.trans
        (uniformSphericalShellMomentMomentumRelation setup _scenario _physical
          _geometry _laws units)
    rw [uniformSphericalShellAngularMomentum setup _scenario _physical _geometry
      _laws units] at hv
    have hs := congrArg (fun v : SpatialVector => v (2 : Fin 3)) hv
    simp only [PiLp.smul_apply, smul_eq_mul, zHat,
      PiLp.single_apply, if_pos, mul_one] at hs
    exact mul_right_cancel₀ (ne_of_gt hLcoeff_pos) hs
  have hm_ne :
      nonnegativeReadout UnitChoices.SI setup.totalMass ≠ 0 :=
    ne_of_gt _physical.positiveMass
  have hq_ne :
      signedReadout UnitChoices.SI setup.totalCharge ≠ 0 :=
    _physical.nonzeroCharge
  have hg_raw :=
    _gyromagnetic.gammaIsGTimesChargeOverTwiceMass UnitChoices.SI
  rw [hgamma UnitChoices.SI] at hg_raw
  have hden_ne :
      2 * nonnegativeReadout UnitChoices.SI setup.totalMass ≠ 0 :=
    mul_ne_zero (by norm_num) hm_ne
  have hq_eq :
      signedReadout UnitChoices.SI setup.totalCharge =
        setup.gFactor * signedReadout UnitChoices.SI setup.totalCharge :=
    (div_left_inj' hden_ne).mp hg_raw
  have hg_one : setup.gFactor = 1 := by
    apply mul_right_cancel₀ hq_ne
    simpa using hq_eq.symm
  refine ⟨hgamma, hg_one, ?_, ?_⟩
  · intro units
    simpa [MatchesDisplayedGyromagneticRatio,
      displayedGyromagneticRatioReadout] using hgamma units
  · intro choice hchoice
    have hc := hchoice UnitChoices.SI
    rw [hgamma UnitChoices.SI] at hc
    cases choice with
    | A =>
        simp [displayedGyromagneticRatioReadout] at hc
        have hzero :
            signedReadout UnitChoices.SI setup.totalCharge = 0 := by
          field_simp [hm_ne] at hc
          linarith
        exact (hq_ne hzero).elim
    | B =>
        rfl
    | C =>
        simp [displayedGyromagneticRatioReadout] at hc
        have hzero :
            signedReadout UnitChoices.SI setup.totalCharge = 0 := by
          field_simp [hm_ne] at hc
          linarith
        exact (hq_ne hzero).elim
    | D =>
        simp [displayedGyromagneticRatioReadout] at hc
        have hzero :
            signedReadout UnitChoices.SI setup.totalCharge = 0 := by
          field_simp [hm_ne] at hc
          linarith
        exact (hq_ne hzero).elim

end PhyXMiniProblems.ProblemPhyXMini0970
