import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0569

/-!
# Recoil speed in head-on photon--electron scattering

An x-ray photon of energy `100 keV` strikes an electron initially at rest.
The primary image shows a one-dimensional backscattering event: before the
collision the photon moves along the positive `x`-axis, while afterwards the
photon moves along the negative `x`-axis and the electron recoils along the
positive `x`-axis.  The requested observable is the electron recoil speed as
a fraction of the vacuum speed of light.

Energies, plane momenta, and speed magnitudes retain their physical
dimensions through Physlib.  Real numbers are used only for named-unit
readouts and dimensionless speed ratios.

Assumption/target boundary:

* `MatchesProblemData` contains the stated `100 keV` photon energy and the
  standard `511 keV` electron rest-energy calibration.
* `MatchesPrimaryBackscatterFigure` contains only the labels, axes, panels,
  and propagation directions visible in the primary image.
* `SatisfiesRelativisticBackscatterLaws` states energy and momentum
  conservation, the photon and electron dispersion laws, and the general
  relativistic momentum--velocity relation.
* There are no previous-part results.
* The derived recoil ratio, the approximation `0.32 c`, and answer C occur
  only in theorem conclusions or in the displayed-answer table.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A dimensionful two-dimensional momentum in the plane of the figure. -/
abbrev PlaneMomentum : Type := Dimensionful (Momentum 2)

/-- The two coordinate axes printed in both panels of the primary image. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The `Fin 2` coordinate corresponding to a printed axis label. -/
def DiagramAxis.toFin : DiagramAxis → Fin 2
  | .x => 0
  | .y => 1

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kilo-electron-volt readout of a physical energy. -/
def energyInKiloElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy /
    (1_000 * energyInJoules DimEnergy.electronVolt)

/-- One momentum component in coherent SI units `kg m / s`. -/
def momentumComponentInSI
    (momentum : PlaneMomentum) (axis : DiagramAxis) : ℝ :=
  (momentum UnitChoices.SI).val axis.toFin

/-- Euclidean magnitude of a plane momentum in `kg m / s`. -/
def momentumMagnitudeInSI (momentum : PlaneMomentum) : ℝ :=
  Real.sqrt
    (momentumComponentInSI momentum .x ^ 2 +
      momentumComponentInSI momentum .y ^ 2)

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Particle states and primary-figure vocabulary -/

/-- A photon state retains both its dimensionful energy and spatial momentum. -/
structure PhotonState where
  energy : DimEnergy
  momentum : PlaneMomentum

/-- The two panels represented side by side in the primary image. -/
inductive FigurePanel where
  | beforeCollision
  | afterCollision
  deriving DecidableEq, Fintype, Repr

/-- Particle labels printed in each panel. -/
inductive ParticleLabel where
  | photon
  | electron
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions visible in the supplied raster. -/
inductive HorizontalMotion where
  | stationary
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-!
Presentation-level information transcribed from the two-panel image.  It
contains no numerical speed, energy, or answer-choice value.
-/
structure PhotonElectronBackscatterFigure where
  panelShown : FigurePanel → Bool
  axisShown : FigurePanel → DiagramAxis → Bool
  particleLabelShown : FigurePanel → ParticleLabel → Bool
  photonMotion : FigurePanel → HorizontalMotion
  electronMotion : FigurePanel → HorizontalMotion
  electronAtAxesIntersectionBefore : Bool

/-!
Independent physical quantities before and after the collision.  The recoil
speed is an unconstrained dimensionful field here; it is related to the
electron's energy and momentum only by the governing law below.
-/
structure PhotonElectronBackscatterSetup where
  incidentPhoton : PhotonState
  scatteredPhoton : PhotonState
  electronRestEnergy : DimEnergy
  initialElectronTotalEnergy : DimEnergy
  recoilingElectronTotalEnergy : DimEnergy
  initialElectronMomentum : PlaneMomentum
  recoilingElectronMomentum : PlaneMomentum
  electronRecoilSpeed : DimSpeed
  electronInitiallyFree : Bool
  figure : PhotonElectronBackscatterFigure

/-! ## Scenario data, figure evidence, and governing laws -/

/-!
Numerical data stated or standard for this instance.  The incident photon has
energy `100 keV`; the standard electron rest energy is calibrated as
`511 keV`.  Neither field specifies the outgoing speed.
-/
structure MatchesProblemData
    (setup : PhotonElectronBackscatterSetup) : Prop where
  incidentPhotonEnergyKeV :
    energyInKiloElectronVolts setup.incidentPhoton.energy = 100
  electronRestEnergyKeV :
    energyInKiloElectronVolts setup.electronRestEnergy = 511
  electronIsInitiallyFree : setup.electronInitiallyFree = true

/-!
Qualitative and directional evidence from the primary image.  In particular,
the outgoing photon reverses direction while the electron recoils to the
right; every physical momentum has zero transverse component.
-/
structure MatchesPrimaryBackscatterFigure
    (setup : PhotonElectronBackscatterSetup) : Prop where
  bothPanelsShown : ∀ panel, setup.figure.panelShown panel = true
  bothAxesShown : ∀ panel axis, setup.figure.axisShown panel axis = true
  bothParticleLabelsShown : ∀ panel particle,
    setup.figure.particleLabelShown panel particle = true
  initialElectronDrawnAtOrigin :
    setup.figure.electronAtAxesIntersectionBefore = true
  incidentPhotonPointsRight :
    setup.figure.photonMotion .beforeCollision = .positiveX
  initialElectronHasNoMotionArrow :
    setup.figure.electronMotion .beforeCollision = .stationary
  scatteredPhotonPointsLeft :
    setup.figure.photonMotion .afterCollision = .negativeX
  recoilingElectronPointsRight :
    setup.figure.electronMotion .afterCollision = .positiveX
  incidentPhotonPositiveXComponent :
    momentumComponentInSI setup.incidentPhoton.momentum .x =
      momentumMagnitudeInSI setup.incidentPhoton.momentum
  incidentPhotonZeroYComponent :
    momentumComponentInSI setup.incidentPhoton.momentum .y = 0
  scatteredPhotonNegativeXComponent :
    momentumComponentInSI setup.scatteredPhoton.momentum .x =
      -momentumMagnitudeInSI setup.scatteredPhoton.momentum
  scatteredPhotonZeroYComponent :
    momentumComponentInSI setup.scatteredPhoton.momentum .y = 0
  recoilingElectronPositiveXComponent :
    momentumComponentInSI setup.recoilingElectronMomentum .x =
      momentumMagnitudeInSI setup.recoilingElectronMomentum
  recoilingElectronZeroYComponent :
    momentumComponentInSI setup.recoilingElectronMomentum .y = 0

/-- Positivity and subluminality conditions for the physical event. -/
structure HasPhysicalBackscatterParameters
    (setup : PhotonElectronBackscatterSetup) : Prop where
  incidentPhotonEnergyPositive :
    0 < energyInJoules setup.incidentPhoton.energy
  scatteredPhotonEnergyPositive :
    0 < energyInJoules setup.scatteredPhoton.energy
  electronRestEnergyPositive :
    0 < energyInJoules setup.electronRestEnergy
  recoilingElectronTotalEnergyPositive :
    0 < energyInJoules setup.recoilingElectronTotalEnergy
  recoilSpeedIsSubluminal :
    speedInMetersPerSecond setup.electronRecoilSpeed <
      speedOfLightInMetersPerSecond

/-!
Governing relations for an isolated relativistic photon--electron collision.
The two photon laws are `E = pc`; the outgoing electron obeys
`E² = (m c²)² + (pc)²` and `v = p c² / E`.  These general relations do not
contain the requested numerical recoil speed.
-/
structure SatisfiesRelativisticBackscatterLaws
    (setup : PhotonElectronBackscatterSetup) : Prop where
  initialElectronAtRest : ∀ axis : DiagramAxis,
    momentumComponentInSI setup.initialElectronMomentum axis = 0
  initialElectronEnergyIsRestEnergy :
    setup.initialElectronTotalEnergy = setup.electronRestEnergy
  momentumConservation : ∀ axis : DiagramAxis,
    momentumComponentInSI setup.incidentPhoton.momentum axis +
        momentumComponentInSI setup.initialElectronMomentum axis =
      momentumComponentInSI setup.scatteredPhoton.momentum axis +
        momentumComponentInSI setup.recoilingElectronMomentum axis
  energyConservation :
    energyInJoules setup.incidentPhoton.energy +
        energyInJoules setup.initialElectronTotalEnergy =
      energyInJoules setup.scatteredPhoton.energy +
        energyInJoules setup.recoilingElectronTotalEnergy
  incidentPhotonEnergyMomentum :
    energyInJoules setup.incidentPhoton.energy =
      speedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.incidentPhoton.momentum
  scatteredPhotonEnergyMomentum :
    energyInJoules setup.scatteredPhoton.energy =
      speedOfLightInMetersPerSecond *
        momentumMagnitudeInSI setup.scatteredPhoton.momentum
  recoilingElectronEnergyMomentum :
    energyInJoules setup.recoilingElectronTotalEnergy ^ 2 =
      energyInJoules setup.electronRestEnergy ^ 2 +
        (speedOfLightInMetersPerSecond *
          momentumMagnitudeInSI setup.recoilingElectronMomentum) ^ 2
  recoilingElectronMomentumVelocity :
    speedInMetersPerSecond setup.electronRecoilSpeed =
      speedOfLightInMetersPerSecond ^ 2 *
          momentumMagnitudeInSI setup.recoilingElectronMomentum /
        energyInJoules setup.recoilingElectronTotalEnergy

/-! ## Recoil observable, displayed choices, and current target -/

/-- The requested dimensionless electron recoil speed `v/c`. -/
def electronRecoilSpeedFractionOfC
    (setup : PhotonElectronBackscatterSetup) : ℝ :=
  speedInMetersPerSecond setup.electronRecoilSpeed /
    speedOfLightInMetersPerSecond

/-!
Conservation and the relativistic dispersion laws determine the exact recoil
ratio for an arbitrary incident photon energy `E` and electron rest energy
`M = m_e c²` in the head-on backscatter geometry:
`v/c = 2 E (E + M) / (M² + 2 M E + 2 E²)`.
-/
lemma electronRecoilSpeedFraction_from_conservation
    (setup : PhotonElectronBackscatterSetup)
    (hFigure : MatchesPrimaryBackscatterFigure setup)
    (hPhysical : HasPhysicalBackscatterParameters setup)
    (hLaws : SatisfiesRelativisticBackscatterLaws setup) :
    electronRecoilSpeedFractionOfC setup =
      (2 * energyInJoules setup.incidentPhoton.energy *
          (energyInJoules setup.incidentPhoton.energy +
            energyInJoules setup.electronRestEnergy)) /
        (energyInJoules setup.electronRestEnergy ^ 2 +
          2 * energyInJoules setup.electronRestEnergy *
            energyInJoules setup.incidentPhoton.energy +
          2 * energyInJoules setup.incidentPhoton.energy ^ 2) := by
  let E : ℝ := energyInJoules setup.incidentPhoton.energy
  let S : ℝ := energyInJoules setup.scatteredPhoton.energy
  let M : ℝ := energyInJoules setup.electronRestEnergy
  let T : ℝ := energyInJoules setup.recoilingElectronTotalEnergy
  let c : ℝ := speedOfLightInMetersPerSecond
  let A : ℝ := momentumMagnitudeInSI setup.incidentPhoton.momentum
  let B : ℝ := momentumMagnitudeInSI setup.scatteredPhoton.momentum
  let P : ℝ := momentumMagnitudeInSI setup.recoilingElectronMomentum
  let V : ℝ := speedInMetersPerSecond setup.electronRecoilSpeed
  have hE : 0 < E := by
    simpa [E] using hPhysical.incidentPhotonEnergyPositive
  have hM : 0 < M := by
    simpa [M] using hPhysical.electronRestEnergyPositive
  have hT_pos : 0 < T := by
    simpa [T] using hPhysical.recoilingElectronTotalEnergyPositive
  have hc : c = 299792458 := by
    change (DimSpeed.speedOfLight UnitChoices.SI).val = 299792458
    rw [DimSpeed.speedOfLight_in_SI]
  have hc_ne : c ≠ 0 := by
    rw [hc]
    norm_num
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hMomentum := hLaws.momentumConservation .x
  rw [hLaws.initialElectronAtRest .x,
    hFigure.incidentPhotonPositiveXComponent,
    hFigure.scatteredPhotonNegativeXComponent,
    hFigure.recoilingElectronPositiveXComponent] at hMomentum
  change A + 0 = -B + P at hMomentum
  have hP : P = A + B := by
    linarith
  have hIncident := hLaws.incidentPhotonEnergyMomentum
  change E = c * A at hIncident
  have hScattered := hLaws.scatteredPhotonEnergyMomentum
  change S = c * B at hScattered
  have hcP : c * P = E + S := by
    calc
      c * P = c * (A + B) := by rw [hP]
      _ = c * A + c * B := by ring
      _ = E + S := by rw [← hIncident, ← hScattered]
  have hEnergy := hLaws.energyConservation
  rw [hLaws.initialElectronEnergyIsRestEnergy] at hEnergy
  change E + M = S + T at hEnergy
  have hT : T = E + M - S := by
    linarith
  have hDispersion := hLaws.recoilingElectronEnergyMomentum
  change T ^ 2 = M ^ 2 + (c * P) ^ 2 at hDispersion
  rw [hcP, hT] at hDispersion
  have hScatterRelation : S * (2 * E + M) = E * M := by
    nlinarith
  have hVelocity := hLaws.recoilingElectronMomentumVelocity
  change V = c ^ 2 * P / T at hVelocity
  have hRatio :
      electronRecoilSpeedFractionOfC setup = c * P / T := by
    change V / c = c * P / T
    rw [hVelocity]
    field_simp [hc_ne, hT_ne]
  have hResultDen_pos :
      0 < M ^ 2 + 2 * M * E + 2 * E ^ 2 := by
    positivity
  have hResultDen_ne :
      M ^ 2 + 2 * M * E + 2 * E ^ 2 ≠ 0 :=
    ne_of_gt hResultDen_pos
  rw [hRatio]
  change
    c * P / T =
      (2 * E * (E + M)) /
        (M ^ 2 + 2 * M * E + 2 * E ^ 2)
  apply (div_eq_div_iff hT_ne hResultDen_ne).2
  rw [hcP, hT]
  linear_combination (2 * E + M) * hScatterRelation

/-- Labels of the four speed choices displayed by the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The numerical coefficient of `c` printed beside each answer label. -/
def displayedSpeedFractionOfC : AnswerChoice → ℝ
  | .A => 11 / 20
  | .B => 19 / 20
  | .C => 8 / 25
  | .D => 51 / 5

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a speed coefficient displayed to the nearest hundredth. -/
def RoundsToNearestHundredth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- A displayed choice is at least as close to the modeled ratio as all others. -/
def IsClosestAnswerChoice (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |actual - displayedSpeedFractionOfC choice| ≤
      |actual - displayedSpeedFractionOfC other|

/-!
**Blueprint label:** `thm:physics:phyx_mini_0569:target`.

For `E = 100 keV` and `m_e c² = 511 keV`, the exact model gives
`v/c = 122200 / 383321 ≈ 0.3188`.  Thus the recoil velocity points along
positive `x`, rounds to `0.32 c`, and uniquely selects answer C.
-/
theorem electronRecoilVelocity_is_choice_C
    (setup : PhotonElectronBackscatterSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesPrimaryBackscatterFigure setup)
    (hPhysical : HasPhysicalBackscatterParameters setup)
    (hLaws : SatisfiesRelativisticBackscatterLaws setup) :
    electronRecoilSpeedFractionOfC setup = (122200 / 383321 : ℝ) ∧
      RoundsToNearestHundredth
        (electronRecoilSpeedFractionOfC setup)
        (displayedSpeedFractionOfC .C) ∧
      IsClosestAnswerChoice
        (electronRecoilSpeedFractionOfC setup) .C ∧
      ∀ choice : AnswerChoice,
        IsClosestAnswerChoice
          (electronRecoilSpeedFractionOfC setup) choice →
        choice = .C := by
  let E : ℝ := energyInJoules setup.incidentPhoton.energy
  let M : ℝ := energyInJoules setup.electronRestEnergy
  let Q : ℝ := 1_000 * energyInJoules DimEnergy.electronVolt
  have hIncidentData := hData.incidentPhotonEnergyKeV
  change E / Q = 100 at hIncidentData
  have hRestData := hData.electronRestEnergyKeV
  change M / Q = 511 at hRestData
  have hQ_ne : Q ≠ 0 := by
    intro hQ
    rw [hQ] at hIncidentData
    norm_num at hIncidentData
  have hE : E = 100 * Q :=
    (div_eq_iff hQ_ne).1 hIncidentData
  have hM : M = 511 * Q :=
    (div_eq_iff hQ_ne).1 hRestData
  have hFormula :=
    electronRecoilSpeedFraction_from_conservation
      setup hFigure hPhysical hLaws
  change
    electronRecoilSpeedFractionOfC setup =
      (2 * E * (E + M)) /
        (M ^ 2 + 2 * M * E + 2 * E ^ 2) at hFormula
  rw [hE, hM] at hFormula
  have hNumerator :
      2 * (100 * Q) * (100 * Q + 511 * Q) =
        122200 * Q ^ 2 := by
    ring
  have hDenominator :
      (511 * Q) ^ 2 + 2 * (511 * Q) * (100 * Q) +
          2 * (100 * Q) ^ 2 =
        383321 * Q ^ 2 := by
    ring
  rw [hNumerator, hDenominator] at hFormula
  have hCancelScale :
      (122200 * Q ^ 2) / (383321 * Q ^ 2) =
        (122200 / 383321 : ℝ) := by
    field_simp [hQ_ne]
  have hExact :
      electronRecoilSpeedFractionOfC setup =
        (122200 / 383321 : ℝ) :=
    hFormula.trans hCancelScale
  refine ⟨hExact, ?_, ?_, ?_⟩
  · rw [hExact]
    norm_num [RoundsToNearestHundredth, displayedSpeedFractionOfC]
  · unfold IsClosestAnswerChoice
    intro other
    rw [hExact]
    cases other <;> norm_num [displayedSpeedFractionOfC]
  · intro choice hClosest
    unfold IsClosestAnswerChoice at hClosest
    rw [hExact] at hClosest
    cases choice with
    | A =>
        have h := hClosest .C
        norm_num [displayedSpeedFractionOfC] at h
    | B =>
        have h := hClosest .C
        norm_num [displayedSpeedFractionOfC] at h
    | C =>
        rfl
    | D =>
        have h := hClosest .C
        norm_num [displayedSpeedFractionOfC] at h

end PhyXMiniProblems.ProblemPhyXMini0569
