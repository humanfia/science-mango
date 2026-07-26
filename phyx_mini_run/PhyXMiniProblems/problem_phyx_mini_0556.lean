import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/-!
# Relativistic decay of particle A into particle B and a photon

Particle A has rest energy `1192 MeV` and travels along the positive `x` axis
at `0.45 c`.  It decays into particle B, whose rest energy is `1116 MeV`, and
a photon.  The supplied figure places B below the positive `x` axis and the
photon above it.  B has speed `0.40 c`, and its displayed direction is
`3.03°` below the axis.  The requested observable is the photon's angle above
the axis.

Energies, speeds, and momenta below are unit-independent dimensionful
Physlib quantities.  Real numbers are used only for unit readouts,
dimensionless speed ratios, plane components, and angles in radians or
degrees.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0556

/-! ## Dimensionful quantities and scalar readouts -/

/-- A unit-independent two-dimensional physical momentum in the plane of the
decay diagram. -/
abbrev PlaneMomentum : Type := Dimensionful (Momentum 2)

/-- The two coordinate directions in the decay diagram. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- The `Fin 2` coordinate corresponding to a labelled diagram axis. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .horizontal => 0
  | .vertical => 1

/-- A momentum component read in coherent SI units, hence in `kg · m / s`. -/
def momentumComponentInSI
    (momentum : PlaneMomentum) (axis : DiagramAxis) : ℝ :=
  (momentum UnitChoices.SI).val axis.toFin

/-- Euclidean magnitude of a plane momentum, read in `kg · m / s`. -/
def momentumMagnitudeInSI (momentum : PlaneMomentum) : ℝ :=
  Real.sqrt
    (momentumComponentInSI momentum .horizontal ^ 2 +
      momentumComponentInSI momentum .vertical ^ 2)

/-- A dimensionful energy read in coherent SI units, hence in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- A dimensionful energy read in megaelectronvolts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000_000 * energyInJoules DimEnergy.electronVolt)

/-- A nonnegative dimensionful speed read in meters per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in meters per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The dimensionless relativistic speed parameter `β = v / c`. -/
def speedFractionOfLight (speed : DimSpeed) : ℝ :=
  speedInMetersPerSecond speed /
    vacuumSpeedOfLightInMetersPerSecond

/-- Convert a radian-valued angle into its degree readout. -/
def angleInDegrees (angleInRadians : ℝ) : ℝ :=
  angleInRadians * 180 / Real.pi

/-- A scalar readout rounds to `reported` at a stated resolution. -/
def RoundsToResolution
    (actual reported resolution : ℝ) : Prop :=
  0 < resolution ∧ |actual - reported| ≤ resolution / 2

/-! ## Particle, event, and primary-figure vocabulary -/

/-- The three particle labels occurring in the decay. -/
inductive ParticleLabel where
  | A
  | B
  | photon
  deriving DecidableEq, Fintype, Repr

/-- The two massive particles to which `E = γ E₀` applies. -/
inductive MassiveParticle where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Regard a massive-particle label as a label in the full decay event. -/
def MassiveParticle.toParticleLabel : MassiveParticle → ParticleLabel
  | .A => .A
  | .B => .B

/-- State immediately before or immediately after the decay. -/
inductive DecayStage where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Which side of the horizontal axis contains a depicted particle path. -/
inductive PathSide where
  | onAxis
  | aboveAxis
  | belowAxis
  deriving DecidableEq, Repr

/-- Direction of the positive horizontal reference axis. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Literal labels and geometric annotations visible in the supplied image. -/
structure RelativisticDecayFigure where
  printedParticleLabel : ParticleLabel → String
  pathSide : ParticleLabel → PathSide
  positiveHorizontalDirection : HorizontalDirection
  printedSpeedFractionOfLight : ParticleLabel → Option ℝ
  printedParticleBAngleDegrees : ℝ
  printedPhotonAngleSymbol : String
  pathsShareDecayVertex : Bool

/-!
The physical quantities in the event.  Rest and total energies are distinct
fields.  The photon angle is likewise an independent observable rather than
a definition involving an answer choice.
-/
structure RelativisticDecaySetup where
  figure : RelativisticDecayFigure
  particlePresentAt : DecayStage → ParticleLabel → Bool
  particleARestEnergy : DimEnergy
  particleBRestEnergy : DimEnergy
  particleASpeed : DimSpeed
  particleBSpeed : DimSpeed
  particleATotalEnergy : DimEnergy
  particleBTotalEnergy : DimEnergy
  photonEnergy : DimEnergy
  particleAMomentum : PlaneMomentum
  particleBMomentum : PlaneMomentum
  photonMomentum : PlaneMomentum
  particleBAngleBelowPositiveX : ℝ
  photonAngleAbovePositiveX : ℝ

/-- Rest energy of one of the two massive particles. -/
def massiveRestEnergy
    (setup : RelativisticDecaySetup) : MassiveParticle → DimEnergy
  | .A => setup.particleARestEnergy
  | .B => setup.particleBRestEnergy

/-- Laboratory-frame speed of one of the two massive particles. -/
def massiveSpeed
    (setup : RelativisticDecaySetup) : MassiveParticle → DimSpeed
  | .A => setup.particleASpeed
  | .B => setup.particleBSpeed

/-- Laboratory-frame total energy of one of the two massive particles. -/
def massiveTotalEnergy
    (setup : RelativisticDecaySetup) : MassiveParticle → DimEnergy
  | .A => setup.particleATotalEnergy
  | .B => setup.particleBTotalEnergy

/-- Laboratory-frame plane momentum of one of the two massive particles. -/
def massiveMomentum
    (setup : RelativisticDecaySetup) : MassiveParticle → PlaneMomentum
  | .A => setup.particleAMomentum
  | .B => setup.particleBMomentum

/-! ## Scenario, figure evidence, and numerical readouts -/

/-- Particle A exists before the decay and disappears; particle B and the
photon are the two products present afterward. -/
structure MatchesTwoBodyDecayScenario
    (setup : RelativisticDecaySetup) : Prop where
  particleABefore : setup.particlePresentAt .before .A = true
  particleBBeforeAbsent : setup.particlePresentAt .before .B = false
  photonBeforeAbsent : setup.particlePresentAt .before .photon = false
  particleAAfterAbsent : setup.particlePresentAt .after .A = false
  particleBAfter : setup.particlePresentAt .after .B = true
  photonAfter : setup.particlePresentAt .after .photon = true

/-!
Primary-image evidence.  Besides the literal labels and branch placement,
the component equations state what it means for the displayed angles to be
measured above or below the positive `x` axis.
-/
structure MatchesSuppliedDecayFigure
    (setup : RelativisticDecaySetup) : Prop where
  particleALabel : setup.figure.printedParticleLabel .A = "A"
  particleBLabel : setup.figure.printedParticleLabel .B = "B"
  photonLabel : setup.figure.printedParticleLabel .photon = "photon"
  particleAOnAxis : setup.figure.pathSide .A = .onAxis
  particleBBelowAxis : setup.figure.pathSide .B = .belowAxis
  photonAboveAxis : setup.figure.pathSide .photon = .aboveAxis
  positiveXAxisPointsRight :
    setup.figure.positiveHorizontalDirection = .rightward
  pathsMeetAtDecayVertex : setup.figure.pathsShareDecayVertex = true
  particleASpeedLabel :
    setup.figure.printedSpeedFractionOfLight .A = some (9 / 20 : ℝ)
  particleBSpeedLabel :
    setup.figure.printedSpeedFractionOfLight .B = some (2 / 5 : ℝ)
  noPhotonSpeedLabel :
    setup.figure.printedSpeedFractionOfLight .photon = none
  particleBAngleLabel :
    setup.figure.printedParticleBAngleDegrees = 303 / 100
  photonAngleIsTheta : setup.figure.printedPhotonAngleSymbol = "θ"
  particleAHorizontalComponent :
    momentumComponentInSI setup.particleAMomentum .horizontal =
      momentumMagnitudeInSI setup.particleAMomentum
  particleAVerticalComponent :
    momentumComponentInSI setup.particleAMomentum .vertical = 0
  particleBHorizontalComponent :
    momentumComponentInSI setup.particleBMomentum .horizontal =
      momentumMagnitudeInSI setup.particleBMomentum *
        Real.cos setup.particleBAngleBelowPositiveX
  particleBVerticalComponent :
    momentumComponentInSI setup.particleBMomentum .vertical =
      -(momentumMagnitudeInSI setup.particleBMomentum *
        Real.sin setup.particleBAngleBelowPositiveX)
  photonHorizontalComponent :
    momentumComponentInSI setup.photonMomentum .horizontal =
      momentumMagnitudeInSI setup.photonMomentum *
        Real.cos setup.photonAngleAbovePositiveX
  photonVerticalComponent :
    momentumComponentInSI setup.photonMomentum .vertical =
      momentumMagnitudeInSI setup.photonMomentum *
        Real.sin setup.photonAngleAbovePositiveX

/-!
Numerical problem data.  The rest energies and speed ratios are the stated
idealized values.  The displayed `3.03°` direction is a two-decimal readout
of the physical B direction; this avoids treating a rounded annotation as an
additional exact conservation equation.
-/
structure MatchesProblemReadouts
    (setup : RelativisticDecaySetup) : Prop where
  particleARestEnergyMeV :
    energyInMegaElectronVolts setup.particleARestEnergy = 1192
  particleBRestEnergyMeV :
    energyInMegaElectronVolts setup.particleBRestEnergy = 1116
  particleASpeedFraction :
    speedFractionOfLight setup.particleASpeed = 9 / 20
  particleBSpeedFraction :
    speedFractionOfLight setup.particleBSpeed = 2 / 5
  particleBAngleMatchesFigure :
    RoundsToResolution
      (angleInDegrees setup.particleBAngleBelowPositiveX)
      setup.figure.printedParticleBAngleDegrees
      (1 / 100)

/-- Positivity, subluminality, and the acute-angle branches shown by the
figure.  These select the physical trigonometric branches without fixing the
unknown photon angle numerically. -/
structure HasPhysicalDecayParameters
    (setup : RelativisticDecaySetup) : Prop where
  particleARestEnergyPositive :
    0 < energyInJoules setup.particleARestEnergy
  particleBRestEnergyPositive :
    0 < energyInJoules setup.particleBRestEnergy
  particleATotalEnergyPositive :
    0 < energyInJoules setup.particleATotalEnergy
  particleBTotalEnergyPositive :
    0 < energyInJoules setup.particleBTotalEnergy
  photonEnergyPositive : 0 < energyInJoules setup.photonEnergy
  lightSpeedPositive : 0 < vacuumSpeedOfLightInMetersPerSecond
  massiveSpeedsPositive :
    ∀ particle : MassiveParticle,
      0 < speedFractionOfLight (massiveSpeed setup particle)
  massiveSpeedsSubluminal :
    ∀ particle : MassiveParticle,
      speedFractionOfLight (massiveSpeed setup particle) < 1
  massiveMomentumMagnitudesPositive :
    ∀ particle : MassiveParticle,
      0 < momentumMagnitudeInSI (massiveMomentum setup particle)
  photonMomentumMagnitudePositive :
    0 < momentumMagnitudeInSI setup.photonMomentum
  particleBAnglePositive : 0 < setup.particleBAngleBelowPositiveX
  particleBAngleAcute :
    setup.particleBAngleBelowPositiveX < Real.pi / 2
  photonAnglePositive : 0 < setup.photonAngleAbovePositiveX
  photonAngleAcute : setup.photonAngleAbovePositiveX < Real.pi / 2

/-! ## Governing special-relativistic decay laws -/

/-!
For each massive particle, `E = γ(β) E₀` and
`p c = γ(β) β E₀`.  The photon obeys `E = p c`; total energy and both
components of momentum are conserved at the decay vertex.  These laws are
generic in the independent physical fields and contain no solved angle or
answer choice.
-/
structure SatisfiesRelativisticDecayLaws
    (setup : RelativisticDecaySetup) : Prop where
  massiveParticleTotalEnergy :
    ∀ particle : MassiveParticle,
      energyInJoules (massiveTotalEnergy setup particle) =
        LorentzGroup.γ (speedFractionOfLight (massiveSpeed setup particle)) *
          energyInJoules (massiveRestEnergy setup particle)
  massiveParticleMomentum :
    ∀ particle : MassiveParticle,
      vacuumSpeedOfLightInMetersPerSecond *
          momentumMagnitudeInSI (massiveMomentum setup particle) =
        LorentzGroup.γ (speedFractionOfLight (massiveSpeed setup particle)) *
          speedFractionOfLight (massiveSpeed setup particle) *
          energyInJoules (massiveRestEnergy setup particle)
  photonEnergyMomentum :
    energyInJoules setup.photonEnergy =
      vacuumSpeedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.photonMomentum
  energyConservation :
    energyInJoules setup.particleATotalEnergy =
      energyInJoules setup.particleBTotalEnergy +
        energyInJoules setup.photonEnergy
  momentumConservation : ∀ axis : DiagramAxis,
    momentumComponentInSI setup.particleAMomentum axis =
      momentumComponentInSI setup.particleBMomentum axis +
        momentumComponentInSI setup.photonMomentum axis

/-! ## Derived direction relation and multiple-choice target -/

/-- Momentum conservation determines the tangent of the photon angle from
the independently represented A and B momenta and the displayed branch
geometry. -/
lemma photonAngle_tan_from_momentumConservation
    (setup : RelativisticDecaySetup)
    (hFigure : MatchesSuppliedDecayFigure setup)
    (hPhysical : HasPhysicalDecayParameters setup)
    (hLaws : SatisfiesRelativisticDecayLaws setup) :
    Real.tan setup.photonAngleAbovePositiveX =
      (momentumMagnitudeInSI setup.particleBMomentum *
        Real.sin setup.particleBAngleBelowPositiveX) /
      (momentumMagnitudeInSI setup.particleAMomentum -
        momentumMagnitudeInSI setup.particleBMomentum *
          Real.cos setup.particleBAngleBelowPositiveX) := by
  rw [Real.tan_eq_sin_div_cos]
  have hVert := hLaws.momentumConservation .vertical
  have hHoriz := hLaws.momentumConservation .horizontal
  rw [hFigure.particleAVerticalComponent,
      hFigure.particleBVerticalComponent,
      hFigure.photonVerticalComponent] at hVert
  rw [hFigure.particleAHorizontalComponent,
      hFigure.particleBHorizontalComponent,
      hFigure.photonHorizontalComponent] at hHoriz
  have hCosPos : 0 < Real.cos setup.photonAngleAbovePositiveX :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, hPhysical.photonAnglePositive],
        hPhysical.photonAngleAcute⟩
  have hDen :
      momentumMagnitudeInSI setup.particleAMomentum -
          momentumMagnitudeInSI setup.particleBMomentum *
            Real.cos setup.particleBAngleBelowPositiveX =
        momentumMagnitudeInSI setup.photonMomentum *
          Real.cos setup.photonAngleAbovePositiveX := by
    linarith [hHoriz]
  have hNum :
      momentumMagnitudeInSI setup.particleBMomentum *
          Real.sin setup.particleBAngleBelowPositiveX =
        momentumMagnitudeInSI setup.photonMomentum *
          Real.sin setup.photonAngleAbovePositiveX := by
    linarith [hVert]
  rw [hNum, hDen]
  field_simp [ne_of_gt hPhysical.photonMomentumMagnitudePositive,
    ne_of_gt hCosPos]

/-- Labels of the four angle choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree-valued angle printed beside each answer label. -/
def displayedPhotonAngleDegrees : AnswerChoice → ℝ
  | .A => 49 / 5
  | .B => 21 / 2
  | .C => 133 / 10
  | .D => 127 / 10

/-- The answer label recorded in the source dataset, retained only as
metadata and not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The physical photon angle rounds to the selected one-decimal-degree
answer. -/
def MatchesDisplayedPhotonAngle
    (setup : RelativisticDecaySetup) (choice : AnswerChoice) : Prop :=
  RoundsToResolution
    (angleInDegrees setup.photonAngleAbovePositiveX)
    (displayedPhotonAngleDegrees choice)
    (1 / 10)

/-!
**Blueprint label:** `thm:physics:phyx_mini_0556:target`.

The conserved relativistic energy and momentum, together with the stated
rest energies, speeds, and figure geometry, make the photon angle round to
`12.7°`.  This is answer choice D, and no other displayed choice matches.
-/
theorem problem_phyx_mini_0556
    (setup : RelativisticDecaySetup)
    (hScenario : MatchesTwoBodyDecayScenario setup)
    (hFigure : MatchesSuppliedDecayFigure setup)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalDecayParameters setup)
    (hLaws : SatisfiesRelativisticDecayLaws setup) :
    MatchesDisplayedPhotonAngle setup .D ∧
      ∀ choice : AnswerChoice,
        MatchesDisplayedPhotonAngle setup choice → choice = .D := by
  let pA := momentumMagnitudeInSI setup.particleAMomentum
  let pB := momentumMagnitudeInSI setup.particleBMomentum
  let pγ := momentumMagnitudeInSI setup.photonMomentum
  let φ := setup.particleBAngleBelowPositiveX
  let θ := setup.photonAngleAbovePositiveX
  let c := vacuumSpeedOfLightInMetersPerSecond
  let rA := energyInJoules setup.particleARestEnergy
  let rB := energyInJoules setup.particleBRestEnergy
  let mev := 1_000_000 * energyInJoules DimEnergy.electronVolt

  have hpA : 0 < pA := by
    simpa [pA, massiveMomentum] using
      hPhysical.massiveMomentumMagnitudesPositive .A
  have hpB : 0 < pB := by
    simpa [pB, massiveMomentum] using
      hPhysical.massiveMomentumMagnitudesPositive .B
  have hpγ : 0 < pγ := by
    simpa [pγ] using hPhysical.photonMomentumMagnitudePositive
  have hc : 0 < c := by
    simpa [c] using hPhysical.lightSpeedPositive
  have hφpos : 0 < φ := by
    simpa [φ] using hPhysical.particleBAnglePositive
  have hθpos : 0 < θ := by
    simpa [θ] using hPhysical.photonAnglePositive
  have hφacute : φ < Real.pi / 2 := by
    simpa [φ] using hPhysical.particleBAngleAcute
  have hθacute : θ < Real.pi / 2 := by
    simpa [θ] using hPhysical.photonAngleAcute

  have hcosThreeEighths :=
    Real.cos_bound (x := (3 / 8 : ℝ)) (by norm_num)
  rw [abs_le] at hcosThreeEighths
  have hcosThreeEighthsLower :
      (928 / 1000 : ℝ) < Real.cos (3 / 8 : ℝ) := by
    norm_num at hcosThreeEighths ⊢
    linarith only [hcosThreeEighths.1]
  have hcosThreeFourths :
      Real.cos (3 / 4 : ℝ) =
        2 * Real.cos (3 / 8 : ℝ) ^ 2 - 1 := by
    convert Real.cos_two_mul (3 / 8 : ℝ) using 1 <;> norm_num
  have hcosThreeFourthsLower :
      (18 / 25 : ℝ) < Real.cos (3 / 4 : ℝ) := by
    rw [hcosThreeFourths]
    nlinarith only [hcosThreeEighthsLower,
      sq_nonneg (Real.cos (3 / 8 : ℝ) - 928 / 1000)]
  have hcosThreeHalves :
      Real.cos (3 / 2 : ℝ) =
        2 * Real.cos (3 / 4 : ℝ) ^ 2 - 1 := by
    convert Real.cos_two_mul (3 / 4 : ℝ) using 1 <;> norm_num
  have hcosThreeHalvesPos : 0 < Real.cos (3 / 2 : ℝ) := by
    rw [hcosThreeHalves]
    nlinarith only [hcosThreeFourthsLower,
      sq_nonneg (Real.cos (3 / 4 : ℝ) - 18 / 25)]
  have hpiLower : (3 : ℝ) < Real.pi := by
    by_contra h
    have hnonpos : Real.cos (3 / 2 : ℝ) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · linarith only [h]
      · nlinarith only [Real.two_le_pi]
    linarith only [hcosThreeHalvesPos, hnonpos]

  have hφround := hData.particleBAngleMatchesFigure
  rw [hFigure.particleBAngleLabel] at hφround
  change
    0 < (1 / 100 : ℝ) ∧
      |φ * 180 / Real.pi - 303 / 100| ≤ (1 / 100 : ℝ) / 2 at hφround
  rw [abs_le] at hφround
  have hφdegLower : (3025 / 1000 : ℝ) ≤ φ * 180 / Real.pi := by
    nlinarith only [hφround.2.1]
  have hφdegUpper : φ * 180 / Real.pi ≤ (3035 / 1000 : ℝ) := by
    nlinarith only [hφround.2.2]
  have hφradLower : (121 / 2400 : ℝ) < φ := by
    have h := (le_div_iff₀ Real.pi_pos).mp hφdegLower
    nlinarith only [h, hpiLower]
  have hφradUpper : φ < (68 / 1000 : ℝ) := by
    have h := (div_le_iff₀ Real.pi_pos).mp hφdegUpper
    nlinarith only [h, Real.pi_le_four]

  have hrAdiv := hData.particleARestEnergyMeV
  have hrBdiv := hData.particleBRestEnergyMeV
  change rA / mev = 1192 at hrAdiv
  change rB / mev = 1116 at hrBdiv
  have hmevne : mev ≠ 0 := by
    intro h
    rw [h] at hrAdiv
    norm_num at hrAdiv
  have hrA : rA = 1192 * mev := by
    field_simp [hmevne] at hrAdiv
    simpa [mul_comm] using hrAdiv
  have hrB : rB = 1116 * mev := by
    field_simp [hmevne] at hrBdiv
    simpa [mul_comm] using hrBdiv
  have hrApos : 0 < rA := by
    simpa [rA] using hPhysical.particleARestEnergyPositive
  have hmevpos : 0 < mev := by
    rw [hrA] at hrApos
    nlinarith only [hrApos]

  have hγApos : 0 < LorentzGroup.γ (9 / 20 : ℝ) := by
    rw [LorentzGroup.γ]
    positivity
  have hγBpos : 0 < LorentzGroup.γ (2 / 5 : ℝ) := by
    rw [LorentzGroup.γ]
    positivity
  have hγAsq :=
    LorentzGroup.γ_sq (9 / 20 : ℝ) (by norm_num)
  have hγBsq :=
    LorentzGroup.γ_sq (2 / 5 : ℝ) (by norm_num)
  norm_num at hγAsq hγBsq
  have hγALower :
      (11197850 / 10000000 : ℝ) <
        LorentzGroup.γ (9 / 20 : ℝ) := by
    nlinarith only [hγAsq, hγApos, sq_nonneg
      (LorentzGroup.γ (9 / 20 : ℝ) - 11197850 / 10000000)]
  have hγAUpper :
      LorentzGroup.γ (9 / 20 : ℝ) <
        (11197851 / 10000000 : ℝ) := by
    nlinarith only [hγAsq, hγApos, sq_nonneg
      (LorentzGroup.γ (9 / 20 : ℝ) - 11197851 / 10000000)]
  have hγBLower :
      (10910894 / 10000000 : ℝ) <
        LorentzGroup.γ (2 / 5 : ℝ) := by
    nlinarith only [hγBsq, hγBpos, sq_nonneg
      (LorentzGroup.γ (2 / 5 : ℝ) - 10910894 / 10000000)]
  have hγBUpper :
      LorentzGroup.γ (2 / 5 : ℝ) <
        (10910895 / 10000000 : ℝ) := by
    nlinarith only [hγBsq, hγBpos, sq_nonneg
      (LorentzGroup.γ (2 / 5 : ℝ) - 10910895 / 10000000)]

  have hE_A := hLaws.massiveParticleTotalEnergy .A
  have hE_B := hLaws.massiveParticleTotalEnergy .B
  change energyInJoules setup.particleATotalEnergy =
    LorentzGroup.γ (speedFractionOfLight setup.particleASpeed) * rA at hE_A
  change energyInJoules setup.particleBTotalEnergy =
    LorentzGroup.γ (speedFractionOfLight setup.particleBSpeed) * rB at hE_B
  rw [hData.particleASpeedFraction] at hE_A
  rw [hData.particleBSpeedFraction] at hE_B
  have hpA_law := hLaws.massiveParticleMomentum .A
  have hpB_law := hLaws.massiveParticleMomentum .B
  change c * pA =
    LorentzGroup.γ (speedFractionOfLight setup.particleASpeed) *
      speedFractionOfLight setup.particleASpeed * rA at hpA_law
  change c * pB =
    LorentzGroup.γ (speedFractionOfLight setup.particleBSpeed) *
      speedFractionOfLight setup.particleBSpeed * rB at hpB_law
  rw [hData.particleASpeedFraction] at hpA_law
  rw [hData.particleBSpeedFraction] at hpB_law
  have hpγ_law := hLaws.photonEnergyMomentum
  change energyInJoules setup.photonEnergy = c * pγ at hpγ_law
  have henergy := hLaws.energyConservation
  have hpγ_energy :
      c * pγ =
        LorentzGroup.γ (9 / 20 : ℝ) * rA -
          LorentzGroup.γ (2 / 5 : ℝ) * rB := by
    rw [hE_A, hE_B, hpγ_law] at henergy
    linarith only [henergy]
  have hpA_scaled :
      c * pA =
        ((2682 / 5 : ℝ) * LorentzGroup.γ (9 / 20 : ℝ)) * mev := by
    calc
      c * pA =
          LorentzGroup.γ (9 / 20 : ℝ) * (9 / 20 : ℝ) *
            (1192 * mev) := by simpa [hrA] using hpA_law
      _ = ((2682 / 5 : ℝ) * LorentzGroup.γ (9 / 20 : ℝ)) * mev := by ring
  have hpB_scaled :
      c * pB =
        ((2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by
    calc
      c * pB =
          LorentzGroup.γ (2 / 5 : ℝ) * (2 / 5 : ℝ) *
            (1116 * mev) := by simpa [hrB] using hpB_law
      _ = ((2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by ring
  have hpγ_scaled :
      c * pγ =
        (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
          1116 * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by
    calc
      c * pγ =
          LorentzGroup.γ (9 / 20 : ℝ) * (1192 * mev) -
            LorentzGroup.γ (2 / 5 : ℝ) * (1116 * mev) := by
              simpa [hrA, hrB] using hpγ_energy
      _ = (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
          1116 * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by ring

  have hpBcoeffLower :
      (83167 / 20000 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) <
        (2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ) := by
    linarith only [hγALower, hγAUpper, hγBLower, hγBUpper]
  have hpBcoeffUpper :
      (2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ) <
        (4159 / 1000 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) := by
    linarith only [hγALower, hγAUpper, hγBLower, hγBUpper]
  have hpAcoeffLower :
      (641 / 125 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) <
        (2682 / 5 : ℝ) * LorentzGroup.γ (9 / 20 : ℝ) := by
    linarith only [hγALower, hγAUpper, hγBLower, hγBUpper]
  have hpBLower : (83167 / 20000 : ℝ) * pγ < pB := by
    have h := mul_lt_mul_of_pos_right hpBcoeffLower hmevpos
    have hscaled :
        c * ((83167 / 20000 : ℝ) * pγ) < c * pB := by
      calc
        c * ((83167 / 20000 : ℝ) * pγ) =
          (83167 / 20000 : ℝ) * (c * pγ) := by ring
        _ = (83167 / 20000 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by
              rw [hpγ_scaled]
              ring
        _ < (2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ) * mev := h
        _ = c * pB := hpB_scaled.symm
    nlinarith only [hscaled, hc]
  have hpBUpper : pB < (4159 / 1000 : ℝ) * pγ := by
    have h := mul_lt_mul_of_pos_right hpBcoeffUpper hmevpos
    have hscaled :
        c * pB < c * ((4159 / 1000 : ℝ) * pγ) := by
      calc
        c * pB =
          (2232 / 5 : ℝ) * LorentzGroup.γ (2 / 5 : ℝ) * mev :=
        hpB_scaled
        _ < (4159 / 1000 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) * mev := h
        _ = (4159 / 1000 : ℝ) * (c * pγ) := by
          rw [hpγ_scaled]
          ring
        _ = c * ((4159 / 1000 : ℝ) * pγ) := by ring
    nlinarith only [hscaled, hc]
  have hpALower : (641 / 125 : ℝ) * pγ < pA := by
    have h := mul_lt_mul_of_pos_right hpAcoeffLower hmevpos
    have hscaled :
        c * ((641 / 125 : ℝ) * pγ) < c * pA := by
      calc
        c * ((641 / 125 : ℝ) * pγ) =
          (641 / 125 : ℝ) * (c * pγ) := by ring
        _ = (641 / 125 : ℝ) *
          (1192 * LorentzGroup.γ (9 / 20 : ℝ) -
            1116 * LorentzGroup.γ (2 / 5 : ℝ)) * mev := by
              rw [hpγ_scaled]
              ring
        _ < (2682 / 5 : ℝ) * LorentzGroup.γ (9 / 20 : ℝ) * mev := h
        _ = c * pA := hpA_scaled.symm
    nlinarith only [hscaled, hc]

  have hVert := hLaws.momentumConservation .vertical
  have hHoriz := hLaws.momentumConservation .horizontal
  change momentumComponentInSI setup.particleAMomentum .vertical =
    momentumComponentInSI setup.particleBMomentum .vertical +
      momentumComponentInSI setup.photonMomentum .vertical at hVert
  change momentumComponentInSI setup.particleAMomentum .horizontal =
    momentumComponentInSI setup.particleBMomentum .horizontal +
      momentumComponentInSI setup.photonMomentum .horizontal at hHoriz
  rw [hFigure.particleAVerticalComponent,
      hFigure.particleBVerticalComponent,
      hFigure.photonVerticalComponent] at hVert
  rw [hFigure.particleAHorizontalComponent,
      hFigure.particleBHorizontalComponent,
      hFigure.photonHorizontalComponent] at hHoriz
  change 0 = -(pB * Real.sin φ) + pγ * Real.sin θ at hVert
  change pA = pB * Real.cos φ + pγ * Real.cos θ at hHoriz
  have hVertEq : pB * Real.sin φ = pγ * Real.sin θ := by
    linarith only [hVert]
  have hCosSum :
      pA ^ 2 - pB ^ 2 - pγ ^ 2 =
        2 * pB * pγ * Real.cos (φ + θ) := by
    rw [Real.cos_add]
    have hh := congrArg (fun x : ℝ => x ^ 2) hHoriz
    have hv := congrArg (fun x : ℝ => x ^ 2) hVertEq
    have hcross :=
      congrArg (fun x : ℝ => x * (pγ * Real.sin θ)) hVertEq
    have hφtrig := Real.sin_sq_add_cos_sq φ
    have hθtrig := Real.sin_sq_add_cos_sq θ
    ring_nf at hh hv hcross hφtrig hθtrig ⊢
    nlinarith only [hh, hv, hcross, hφtrig, hθtrig]
  have hCosSumLower :
      (9612 / 10000 : ℝ) < Real.cos (φ + θ) := by
    by_contra h
    have hcosle : Real.cos (φ + θ) ≤ (9612 / 10000 : ℝ) :=
      le_of_not_gt h
    have hfactor : 0 ≤ (2 * pB * pγ : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hpB.le) hpγ.le
    have hcosmul :=
      mul_le_mul_of_nonneg_left hcosle hfactor
    have hpAprod :
        0 <
          (pA - (641 / 125 : ℝ) * pγ) *
            (pA + (641 / 125 : ℝ) * pγ) := by
      exact mul_pos (sub_pos.mpr hpALower)
        (add_pos hpA
          (mul_pos (by norm_num : (0 : ℝ) < 641 / 125) hpγ))
    have hpAsq :
        ((641 / 125 : ℝ) * pγ) ^ 2 < pA ^ 2 := by
      nlinarith only [hpAprod]
    have hpBprod :
        0 <
          ((4159 / 1000 : ℝ) * pγ - pB) *
            ((4159 / 1000 : ℝ) * pγ + pB) := by
      exact mul_pos (sub_pos.mpr hpBUpper)
        (add_pos
          (mul_pos (by norm_num : (0 : ℝ) < 4159 / 1000) hpγ) hpB)
    have hpBsq :
        pB ^ 2 < ((4159 / 1000 : ℝ) * pγ) ^ 2 := by
      nlinarith only [hpBprod]
    nlinarith only [hCosSum, hcosmul, hpAsq, hpBsq,
      hpBUpper, sq_pos_of_pos hpγ]
  have hcosSevenTwentyFifths :=
    Real.cos_bound (x := (7 / 25 : ℝ)) (by norm_num)
  rw [abs_le] at hcosSevenTwentyFifths
  have hcosSevenTwentyFifthsUpper :
      Real.cos (7 / 25 : ℝ) < (9612 / 10000 : ℝ) := by
    norm_num at hcosSevenTwentyFifths ⊢
    linarith only [hcosSevenTwentyFifths.2]
  have hsumUpper : φ + θ < (7 / 25 : ℝ) := by
    by_contra h
    have hcosle :
        Real.cos (φ + θ) ≤ Real.cos (7 / 25 : ℝ) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · norm_num
      · nlinarith only [hφacute, hθacute]
      · exact le_of_not_gt h
    linarith only [hCosSumLower, hcosSevenTwentyFifthsUpper, hcosle]
  have hθradUpper : θ < (23 / 100 : ℝ) := by
    nlinarith only [hφradLower, hsumUpper]

  have hφsqUpper : φ ^ 2 < (68 / 1000 : ℝ) ^ 2 := by
    have hprod :
        0 < ((68 / 1000 : ℝ) - φ) * ((68 / 1000 : ℝ) + φ) :=
      mul_pos (sub_pos.mpr hφradUpper)
        (add_pos (by norm_num : (0 : ℝ) < 68 / 1000) hφpos)
    nlinarith only [hprod]
  have hφcubeUpper : φ ^ 3 < (68 / 1000 : ℝ) ^ 3 := by
    calc
      φ ^ 3 = φ ^ 2 * φ := by ring
      _ < (68 / 1000 : ℝ) ^ 2 * (68 / 1000 : ℝ) :=
        mul_lt_mul hφsqUpper hφradUpper.le hφpos (by norm_num)
      _ = (68 / 1000 : ℝ) ^ 3 := by ring
  have hsinφBound := Real.sin_bound (x := φ) (by
    rw [abs_of_pos hφpos]
    linarith only [hφradUpper])
  rw [abs_le] at hsinφBound
  have hsinφLower : (999 / 1000 : ℝ) * φ < Real.sin φ := by
    have herr :
        φ ^ 2 / 6 + φ ^ 3 * (5 / 96 : ℝ) < 1 / 1000 := by
      nlinarith only [hφsqUpper, hφcubeUpper]
    have herrmul := mul_lt_mul_of_pos_right herr hφpos
    rw [abs_of_pos hφpos] at hsinφBound
    nlinarith only [herrmul, hsinφBound.1]
  have hsinφUpper : Real.sin φ ≤ φ := by
    have hcoef : φ * (5 / 96 : ℝ) ≤ 1 / 6 := by
      nlinarith only [hφradUpper]
    have hmul := mul_le_mul_of_nonneg_left hcoef
      (by positivity : 0 ≤ φ ^ 3)
    rw [abs_of_pos hφpos] at hsinφBound
    nlinarith only [hmul, hsinφBound.2]
  have hsinφpos : 0 < Real.sin φ := by
    nlinarith only [hsinφLower, hφpos]

  have hθsqUpper : θ ^ 2 < (23 / 100 : ℝ) ^ 2 := by
    have hprod :
        0 < ((23 / 100 : ℝ) - θ) * ((23 / 100 : ℝ) + θ) :=
      mul_pos (sub_pos.mpr hθradUpper)
        (add_pos (by norm_num : (0 : ℝ) < 23 / 100) hθpos)
    nlinarith only [hprod]
  have hθcubeUpper : θ ^ 3 < (23 / 100 : ℝ) ^ 3 := by
    calc
      θ ^ 3 = θ ^ 2 * θ := by ring
      _ < (23 / 100 : ℝ) ^ 2 * (23 / 100 : ℝ) :=
        mul_lt_mul hθsqUpper hθradUpper.le hθpos (by norm_num)
      _ = (23 / 100 : ℝ) ^ 3 := by ring
  have hsinθBound := Real.sin_bound (x := θ) (by
    rw [abs_of_pos hθpos]
    linarith only [hθradUpper])
  rw [abs_of_pos hθpos, abs_le] at hsinθBound
  have hsinθLower : (9905 / 10000 : ℝ) * θ < Real.sin θ := by
    have herr :
        θ ^ 2 / 6 + θ ^ 3 * (5 / 96 : ℝ) < 95 / 10000 := by
      nlinarith only [hθsqUpper, hθcubeUpper]
    have herrmul := mul_lt_mul_of_pos_right herr hθpos
    nlinarith only [herrmul, hsinθBound.1]
  have hsinθUpper : Real.sin θ ≤ θ := by
    have hcoef : θ * (5 / 96 : ℝ) ≤ 1 / 6 := by
      nlinarith only [hθradUpper]
    have hmul := mul_le_mul_of_nonneg_left hcoef
      (by positivity : 0 ≤ θ ^ 3)
    nlinarith only [hmul, hsinθBound.2]
  have hsinRatioLower :
      (83167 / 20000 : ℝ) * Real.sin φ < Real.sin θ := by
    have hmul := mul_lt_mul_of_pos_right hpBLower hsinφpos
    rw [hVertEq] at hmul
    nlinarith only [hmul, hpγ]
  have hsinRatioUpper :
      Real.sin θ < (4159 / 1000 : ℝ) * Real.sin φ := by
    have hmul := mul_lt_mul_of_pos_right hpBUpper hsinφpos
    rw [hVertEq] at hmul
    nlinarith only [hmul, hpγ]
  have hθradLower : (1047 / 5000 : ℝ) < θ := by
    nlinarith only [hsinRatioLower, hsinφLower, hφradLower, hsinθUpper]
  have hθsqLower : (1047 / 5000 : ℝ) ^ 2 < θ ^ 2 := by
    have hprod :
        0 <
          (θ - (1047 / 5000 : ℝ)) *
            (θ + (1047 / 5000 : ℝ)) :=
      mul_pos (sub_pos.mpr hθradLower)
        (add_pos hθpos (by norm_num : (0 : ℝ) < 1047 / 5000))
    nlinarith only [hprod]
  have hsinθUpperSharp :
      Real.sin θ < (99333 / 100000 : ℝ) * θ := by
    have herr :
        667 / 100000 <
          θ ^ 2 / 6 - θ ^ 3 * (5 / 96 : ℝ) := by
      nlinarith only [hθsqLower, hθcubeUpper]
    have herrmul := mul_lt_mul_of_pos_right herr hθpos
    nlinarith only [herrmul, hsinθBound.2]

  have hangleRatioLower :
      (83167 / 20000 : ℝ) * (999 / 1000 : ℝ) * φ <
        (99333 / 100000 : ℝ) * θ := by
    nlinarith only [hsinRatioLower, hsinφLower, hsinθUpperSharp]
  have hangleRatioUpper :
      (9905 / 10000 : ℝ) * θ <
        (4159 / 1000 : ℝ) * φ := by
    nlinarith only [hsinRatioUpper, hsinφUpper, hsinθLower]
  have hdegreeScale : 0 < (180 / Real.pi : ℝ) :=
    div_pos (by norm_num) Real.pi_pos
  have hangleRatioLowerDeg :=
    mul_lt_mul_of_pos_right hangleRatioLower hdegreeScale
  have hangleRatioUpperDeg :=
    mul_lt_mul_of_pos_right hangleRatioUpper hdegreeScale
  have hangleRatioLowerDeg' :
      (83167 / 20000 : ℝ) * (999 / 1000 : ℝ) *
          (φ * 180 / Real.pi) <
        (99333 / 100000 : ℝ) * (θ * 180 / Real.pi) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hangleRatioLowerDeg
  have hangleRatioUpperDeg' :
      (9905 / 10000 : ℝ) * (θ * 180 / Real.pi) <
        (4159 / 1000 : ℝ) * (φ * 180 / Real.pi) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hangleRatioUpperDeg
  have hθdegLower : (253 / 20 : ℝ) < θ * 180 / Real.pi := by
    nlinarith only [hangleRatioLowerDeg', hφdegLower]
  have hθdegUpper : θ * 180 / Real.pi < (51 / 4 : ℝ) := by
    nlinarith only [hangleRatioUpperDeg', hφdegUpper]

  constructor
  · change
      0 < (1 / 10 : ℝ) ∧
        |θ * 180 / Real.pi - 127 / 10| ≤ (1 / 10 : ℝ) / 2
    constructor
    · norm_num
    · rw [abs_le]
      constructor <;> nlinarith only [hθdegLower, hθdegUpper]
  · intro choice hchoice
    cases choice with
    | A =>
        change
          0 < (1 / 10 : ℝ) ∧
            |θ * 180 / Real.pi - 49 / 5| ≤ (1 / 10 : ℝ) / 2 at hchoice
        rw [abs_le] at hchoice
        exfalso
        nlinarith only [hchoice.2.2, hθdegLower]
    | B =>
        change
          0 < (1 / 10 : ℝ) ∧
            |θ * 180 / Real.pi - 21 / 2| ≤ (1 / 10 : ℝ) / 2 at hchoice
        rw [abs_le] at hchoice
        exfalso
        nlinarith only [hchoice.2.2, hθdegLower]
    | C =>
        change
          0 < (1 / 10 : ℝ) ∧
            |θ * 180 / Real.pi - 133 / 10| ≤ (1 / 10 : ℝ) / 2 at hchoice
        rw [abs_le] at hchoice
        exfalso
        nlinarith only [hchoice.2.1, hθdegUpper]
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0556
