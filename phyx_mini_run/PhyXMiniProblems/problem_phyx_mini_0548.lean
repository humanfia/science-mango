import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.SpaceAndTime.Space.Module
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0548

open Dimension

/-!
# Photon scattering from a stationary free electron

An incident photon of frequency `ν` scatters from a stationary free electron.
The primary figure shows the incident photon moving horizontally to the right,
the scattered photon moving upward and to the right, and the angle `θ` between
their propagation directions.

Frequencies, energies, momenta, the electron rest mass, and Planck's constant
are represented by dimensionful quantities.  Real numbers occur only as
coherent-SI readouts, direction coordinates, and the angle in radians.  The
outgoing frequency is an independent field of the setup; it is not defined by
the requested Compton formula or by the recorded answer choice.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent ordinary frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical quantity of action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent physical two-momentum in the plane of the figure. -/
abbrev DimMomentum2D : Type :=
  Dimensionful (Momentum 2)

/-- Read an ordinary frequency in coherent SI units (hertz). -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read an energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an action in coherent SI units (joule-seconds). -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read a mass in coherent SI units (kilograms). -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical two-momentum in coherent SI momentum coordinates. -/
def momentumInSI (momentum : DimMomentum2D) : Space 2 :=
  ⟨(momentum UnitChoices.SI).val⟩

/-- The Physlib speed of light, read in coherent SI units (meters per second). -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The undirected angle in radians between two physical unit directions. -/
def directionAngle (first second : Space.Direction 2) : ℝ :=
  InnerProductGeometry.angle first.unit second.unit

/-! ## Particle states and labels -/

/-- The photon-frequency labels visible in the supplied figure. -/
inductive PhotonLabel where
  | nu
  | nuPrime
  deriving DecidableEq, Fintype, Repr

/-- The electron before and after the scattering interaction. -/
inductive ElectronPhase where
  | initial
  | recoil
  deriving DecidableEq, Fintype, Repr

/-- Whether the electron is free or bound before the interaction. -/
inductive ElectronBindingState where
  | free
  | bound
  deriving DecidableEq, Repr

/-- The initial motion state of the target electron. -/
inductive ElectronMotionState where
  | atRest
  | moving
  deriving DecidableEq, Repr

/--
A photon state retains independent physical frequency, energy, momentum, and
propagation direction.  The governing photon laws below relate these fields.
-/
structure PhotonState where
  frequency : FrequencyQuantity
  energy : DimEnergy
  momentum : DimMomentum2D
  propagationDirection : Space.Direction 2

/--
An electron state retains independent relativistic energy and two-momentum.
Both phases use the same rest mass stored in the scattering setup.
-/
structure ElectronState where
  energy : DimEnergy
  momentum : DimMomentum2D

/-! ## Primary-figure data -/

/-- Qualitative features and labels visible in image 548. -/
structure ComptonScatteringFigure where
  showsPhotonLabel : PhotonLabel → Bool
  showsLeftSourcePoint : Bool
  showsScatteringPoint : Bool
  incidentPathPointsRight : Bool
  referenceLineIsHorizontalDashed : Bool
  scatteredPathPointsUpAndRight : Bool
  showsThetaArc : Bool
  showsThetaLabel : Bool

/-!
The independent physical state of the photon-electron system.  In particular,
the scattered photon's frequency is not computed from the incident frequency.
-/
structure ComptonScatteringSetup where
  photon : PhotonLabel → PhotonState
  electron : ElectronPhase → ElectronState
  electronRestMass : MassQuantity
  planckConstant : ActionQuantity
  electronBindingState : ElectronBindingState
  initialElectronMotionState : ElectronMotionState
  scatteringAngleRadians : ℝ
  figure : ComptonScatteringFigure

/-! ## Scenario, figure readouts, and physical laws -/

/--
The target electron is free and stationary before the collision.  Vanishing
initial momentum is the quantitative content of the stationarity readout.
-/
structure MatchesStationaryFreeElectronScenario
    (setup : ComptonScatteringSetup) : Prop where
  electronIsFree : setup.electronBindingState = .free
  electronIsInitiallyAtRest : setup.initialElectronMotionState = .atRest
  initialElectronMomentumIsZero :
    momentumInSI (setup.electron .initial).momentum = 0

/-!
Facts read from the primary image.  `θ` is the angle from the horizontal
incident propagation direction to the upward-right scattered direction.
-/
structure MatchesSuppliedComptonFigure
    (setup : ComptonScatteringSetup) : Prop where
  bothFrequencyLabelsShown :
    ∀ label, setup.figure.showsPhotonLabel label = true
  leftSourcePointShown : setup.figure.showsLeftSourcePoint = true
  scatteringPointShown : setup.figure.showsScatteringPoint = true
  incidentPathPointsRight : setup.figure.incidentPathPointsRight = true
  horizontalDashedReferenceShown :
    setup.figure.referenceLineIsHorizontalDashed = true
  scatteredPathPointsUpAndRight :
    setup.figure.scatteredPathPointsUpAndRight = true
  thetaArcShown : setup.figure.showsThetaArc = true
  thetaLabelShown : setup.figure.showsThetaLabel = true
  thetaReadout :
    setup.scatteringAngleRadians =
      directionAngle
        (setup.photon .nu).propagationDirection
        (setup.photon .nuPrime).propagationDirection

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalComptonParameters
    (setup : ComptonScatteringSetup) : Prop where
  planckConstantPositive :
    0 < actionInJouleSeconds setup.planckConstant
  electronRestMassPositive :
    0 < massInKilograms setup.electronRestMass
  photonFrequenciesPositive :
    ∀ label, 0 < frequencyInHertz (setup.photon label).frequency
  photonEnergiesPositive :
    ∀ label, 0 < energyInJoules (setup.photon label).energy
  electronEnergiesPositive :
    ∀ phase, 0 < energyInJoules (setup.electron phase).energy

/-!
The Planck--Einstein relation `Eγ = hν` for both the incident and scattered
photon.  It is a general law and gives neither frequency the requested value.
-/
structure SatisfiesPlanckEinsteinPhotonLaw
    (setup : ComptonScatteringSetup) : Prop where
  photonEnergyFromFrequency : ∀ label,
    energyInJoules (setup.photon label).energy =
      actionInJouleSeconds setup.planckConstant *
        frequencyInHertz (setup.photon label).frequency

/-!
The massless-photon momentum law `pγ = (Eγ/c) n`, including both its magnitude
and its alignment with the unit propagation direction `n`.
-/
structure SatisfiesMasslessPhotonMomentumLaw
    (setup : ComptonScatteringSetup) : Prop where
  photonMomentumFromEnergy : ∀ label,
    momentumInSI (setup.photon label).momentum =
      (energyInJoules (setup.photon label).energy /
          speedOfLightInMetersPerSecond) •
        (setup.photon label).propagationDirection.unit

/-!
Conservation of total photon-electron energy and vector momentum across the
single scattering event.  These equations do not contain the Compton answer.
-/
structure SatisfiesPhotonElectronConservationLaws
    (setup : ComptonScatteringSetup) : Prop where
  energyConservation :
    energyInJoules (setup.photon .nu).energy +
        energyInJoules (setup.electron .initial).energy =
      energyInJoules (setup.photon .nuPrime).energy +
        energyInJoules (setup.electron .recoil).energy
  momentumConservation :
    momentumInSI (setup.photon .nu).momentum +
        momentumInSI (setup.electron .initial).momentum =
      momentumInSI (setup.photon .nuPrime).momentum +
        momentumInSI (setup.electron .recoil).momentum

/-!
The relativistic energy--momentum relation
`E² = (c ‖p‖)² + (m₀ c²)²` for the same free electron before and after recoil.
-/
structure SatisfiesElectronRelativisticEnergyMomentumRelation
    (setup : ComptonScatteringSetup) : Prop where
  electronDispersion : ∀ phase,
    energyInJoules (setup.electron phase).energy ^ 2 =
      (speedOfLightInMetersPerSecond *
          ‖momentumInSI (setup.electron phase).momentum‖) ^ 2 +
        (massInKilograms setup.electronRestMass *
          speedOfLightInMetersPerSecond ^ 2) ^ 2

/-! ## Displayed answer formulas and target -/

/-- The four answer labels in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The angular factor printed in each answer-choice denominator. -/
def answerAngularFactor (choice : AnswerChoice) (theta : ℝ) : ℝ :=
  match choice with
  | .A => 1 + Real.sin theta
  | .B => 1 - Real.sin theta
  | .C => 1 + Real.cos theta
  | .D => 1 - Real.cos theta

/-!
The outgoing-frequency readout printed for an answer choice.  This is merely
the source's answer table; it does not define the physical scattered photon.
-/
def displayedOutgoingFrequencyInHertz
    (setup : ComptonScatteringSetup) (choice : AnswerChoice) : ℝ :=
  frequencyInHertz (setup.photon .nu).frequency /
    (1 +
      (actionInJouleSeconds setup.planckConstant *
          frequencyInHertz (setup.photon .nu).frequency /
        (massInKilograms setup.electronRestMass *
          speedOfLightInMetersPerSecond ^ 2)) *
      answerAngularFactor choice setup.scatteringAngleRadians)

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Momentum conservation, energy conservation, the massless photon laws, and the
electron relativistic dispersion relation imply the Compton frequency shift.
Thus the scattered frequency is

`ν' = ν / (1 + (hν/(m₀c²)) (1 - cos θ))`,

which is answer D.

This formalizes `thm:physics:phyx_mini_0548:target`.
-/
theorem problem_phyx_mini_0548
    (setup : ComptonScatteringSetup)
    (hScenario : MatchesStationaryFreeElectronScenario setup)
    (hFigure : MatchesSuppliedComptonFigure setup)
    (hPhysical : HasPhysicalComptonParameters setup)
    (hPlanckEinstein : SatisfiesPlanckEinsteinPhotonLaw setup)
    (hPhotonMomentum : SatisfiesMasslessPhotonMomentumLaw setup)
    (hConservation : SatisfiesPhotonElectronConservationLaws setup)
    (hRelativity :
      SatisfiesElectronRelativisticEnergyMomentumRelation setup) :
    frequencyInHertz (setup.photon .nuPrime).frequency =
      frequencyInHertz (setup.photon .nu).frequency /
        (1 +
          (actionInJouleSeconds setup.planckConstant *
              frequencyInHertz (setup.photon .nu).frequency /
            (massInKilograms setup.electronRestMass *
              speedOfLightInMetersPerSecond ^ 2)) *
          (1 - Real.cos setup.scatteringAngleRadians)) := by
  let ν := frequencyInHertz (setup.photon .nu).frequency
  let ν' := frequencyInHertz (setup.photon .nuPrime).frequency
  let h := actionInJouleSeconds setup.planckConstant
  let m := massInKilograms setup.electronRestMass
  let c := speedOfLightInMetersPerSecond
  let Eγ := energyInJoules (setup.photon .nu).energy
  let Eγ' := energyInJoules (setup.photon .nuPrime).energy
  let Ee₀ := energyInJoules (setup.electron .initial).energy
  let Ee' := energyInJoules (setup.electron .recoil).energy
  let pγ := momentumInSI (setup.photon .nu).momentum
  let pγ' := momentumInSI (setup.photon .nuPrime).momentum
  let pe₀ := momentumInSI (setup.electron .initial).momentum
  let pe' := momentumInSI (setup.electron .recoil).momentum
  let u := (setup.photon .nu).propagationDirection.unit
  let u' := (setup.photon .nuPrime).propagationDirection.unit
  let θ := setup.scatteringAngleRadians

  have hc : c = 299792458 := by
    simp [c, speedOfLightInMetersPerSecond]
  have hc_pos : 0 < c := by
    rw [hc]
    norm_num
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hh_pos : 0 < h := by
    simpa [h] using hPhysical.planckConstantPositive
  have hm_pos : 0 < m := by
    simpa [m] using hPhysical.electronRestMassPositive
  have hν_pos : 0 < ν := by
    simpa [ν] using hPhysical.photonFrequenciesPositive .nu
  have hν'_pos : 0 < ν' := by
    simpa [ν'] using hPhysical.photonFrequenciesPositive .nuPrime
  have hEe₀_pos : 0 < Ee₀ := by
    simpa [Ee₀] using hPhysical.electronEnergiesPositive .initial

  have hEγ : Eγ = h * ν := by
    simpa [Eγ, h, ν] using
      hPlanckEinstein.photonEnergyFromFrequency .nu
  have hEγ' : Eγ' = h * ν' := by
    simpa [Eγ', h, ν'] using
      hPlanckEinstein.photonEnergyFromFrequency .nuPrime
  have hpγ : pγ = (Eγ / c) • u := by
    simpa [pγ, Eγ, c, u] using
      hPhotonMomentum.photonMomentumFromEnergy .nu
  have hpγ' : pγ' = (Eγ' / c) • u' := by
    simpa [pγ', Eγ', c, u'] using
      hPhotonMomentum.photonMomentumFromEnergy .nuPrime
  have hpe₀ : pe₀ = 0 := by
    simpa [pe₀] using hScenario.initialElectronMomentumIsZero

  have hEe₀ :
      Ee₀ = m * c ^ 2 := by
    have hdispersion :=
      hRelativity.electronDispersion .initial
    change Ee₀ ^ 2 = (c * ‖pe₀‖) ^ 2 + (m * c ^ 2) ^ 2 at hdispersion
    rw [hpe₀, norm_zero] at hdispersion
    have hmc2_pos : 0 < m * c ^ 2 := mul_pos hm_pos (sq_pos_of_pos hc_pos)
    nlinarith

  have hEe' :
      Ee' = m * c ^ 2 + h * (ν - ν') := by
    have henergy := hConservation.energyConservation
    change Eγ + Ee₀ = Eγ' + Ee' at henergy
    rw [hEγ, hEγ', hEe₀] at henergy
    linarith

  have hpe' :
      pe' = (h * ν / c) • u - (h * ν' / c) • u' := by
    have hmomentum := hConservation.momentumConservation
    change pγ + pe₀ = pγ' + pe' at hmomentum
    rw [hpe₀, add_zero, hpγ, hpγ', hEγ, hEγ'] at hmomentum
    calc
      pe' = (h * ν' / c) • u' + pe' - (h * ν' / c) • u' := by abel
      _ = (h * ν / c) • u - (h * ν' / c) • u' := by rw [← hmomentum]

  have hangle :
      θ = InnerProductGeometry.angle u u' := by
    simpa [θ, u, u', directionAngle] using hFigure.thetaReadout
  have hinner :
      inner ℝ u u' = Real.cos θ := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
      (setup.photon .nu).propagationDirection.norm
      (setup.photon .nuPrime).propagationDirection.norm]
    exact congrArg Real.cos hangle.symm

  have hα_pos : 0 < h * ν / c :=
    div_pos (mul_pos hh_pos hν_pos) hc_pos
  have hβ_pos : 0 < h * ν' / c :=
    div_pos (mul_pos hh_pos hν'_pos) hc_pos
  have hnorm_pe' :
      ‖pe'‖ ^ 2 =
        (h * ν / c) ^ 2 + (h * ν' / c) ^ 2 -
          2 * (h * ν / c) * (h * ν' / c) * Real.cos θ := by
    rw [hpe', norm_sub_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right, hinner,
      (setup.photon .nu).propagationDirection.norm,
      (setup.photon .nuPrime).propagationDirection.norm]
    simp only [Real.norm_eq_abs, abs_of_pos hα_pos, abs_of_pos hβ_pos,
      mul_one]
    ring

  have hrecoilDispersion :=
    hRelativity.electronDispersion .recoil
  change Ee' ^ 2 = (c * ‖pe'‖) ^ 2 + (m * c ^ 2) ^ 2 at hrecoilDispersion
  have hscaledNorm :
      (c * ‖pe'‖) ^ 2 =
        (h * ν) ^ 2 + (h * ν') ^ 2 -
          2 * (h * ν) * (h * ν') * Real.cos θ := by
    rw [mul_pow, hnorm_pe']
    field_simp [hc_ne]
  rw [hEe', hscaledNorm] at hrecoilDispersion

  have hshift :
      m * c ^ 2 * (ν - ν') =
        h * ν * ν' * (1 - Real.cos θ) := by
    have hfactor :
        h * (m * c ^ 2 * (ν - ν') -
          h * ν * ν' * (1 - Real.cos θ)) = 0 := by
      ring_nf at hrecoilDispersion ⊢
      linarith only [hrecoilDispersion]
    rcases mul_eq_zero.mp hfactor with hh | hrest
    · exact False.elim (ne_of_gt hh_pos hh)
    · linarith

  have hdenom_pos :
      0 <
        1 + (h * ν / (m * c ^ 2)) * (1 - Real.cos θ) := by
    have hcos : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
    have hfrac : 0 < h * ν / (m * c ^ 2) :=
      div_pos (mul_pos hh_pos hν_pos) (mul_pos hm_pos (sq_pos_of_pos hc_pos))
    nlinarith only [mul_nonneg (le_of_lt hfrac) hcos]
  apply (eq_div_iff (ne_of_gt hdenom_pos)).2
  change ν' * (1 + h * ν / (m * c ^ 2) * (1 - Real.cos θ)) = ν
  field_simp [ne_of_gt hm_pos, hc_ne]
  linarith only [hshift]

end PhyXMiniProblems.ProblemPhyXMini0548
