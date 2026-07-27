import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/-!
# IPhO 2026 Problem 1 C.2: photodissociation of ozone

The physical quantities in this file use Physlib's dimension-carrying types. Real numbers are
used only for dimensionless angles or for scalar readouts in a specified system of units.
-/

open scoped BigOperators

namespace IPhO2026Problems.IPhO2026_1_C_2

open Dimension
open NNReal

/-- A mass with no preferred system of units. -/
abbrev DimMass : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- An angular frequency, with physical dimension `T⁻¹`, and no preferred system of units. -/
abbrev AngularFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- An action, with physical dimension `M L² T⁻¹`, and no preferred system of units. -/
abbrev DimAction : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) ℝ)

/-- One unified atomic mass unit, represented as a dimensionful mass from its SI readout. -/
noncomputable def atomicMassUnit : DimMass :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨1.66053906892e-27⟩

/-- The reduced Planck constant, represented as a dimensionful action from Physlib's SI value. -/
noncomputable def reducedPlanckConstant : DimAction :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨(Constants.ℏ : ℝ)⟩

/-- The scalar readout of a dimensionful real quantity in a specified system of units. -/
def scalarInUnits {d : Dimension}
    (q : Dimensionful (WithDim d ℝ)) (u : UnitChoices) : ℝ :=
  (q.1 u).val

/-- The scalar SI readout of a dimensionful real quantity. -/
noncomputable def siScalar {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  scalarInUnits q UnitChoices.SI

/-- The squared Euclidean norm of a spatial momentum in its common working units. -/
def momentumSquaredNorm {d : ℕ} (p : Momentum d) : ℝ :=
  ∑ i, (p.val i) ^ 2

/-- The Euclidean dot product of two momenta expressed in the same working units. -/
def momentumDot {d : ℕ} (p q : Momentum d) : ℝ :=
  ∑ i, p.val i * q.val i

/-- `p` makes the dimensionless angle `θ` with the nonzero reference momentum `q`. -/
def MakesAngle {d : ℕ} (p q : Momentum d) (θ : ℝ) : Prop :=
  p ≠ 0 ∧ q ≠ 0 ∧
    momentumDot p q =
      Real.sqrt (momentumSquaredNorm p) *
        Real.sqrt (momentumSquaredNorm q) * Real.cos θ

/--
The named quantities in Figure 1c.

All momenta are expressed in the common unit choice `workingUnits`. The photon at threshold is
absorbed by an initially stationary ozone molecule and produces the displayed outgoing `O₂` and
`O` fragments.
-/
structure OzonePhotodissociationSetup where
  workingUnits : UnitChoices
  theta : ℝ
  atomMass : DimMass
  oxygenMoleculeMass : DimMass
  oxygenAtomMass : DimMass
  initialOzoneGroundEnergy : DimEnergy
  finalOxygenMoleculeGroundEnergy : DimEnergy
  deltaU : DimEnergy
  omegaMin : AngularFrequency
  thresholdPhotonEnergy : DimEnergy
  incidentPhotonMomentum : Momentum 3
  initialOzoneMomentum : Momentum 3
  outgoingOxygenMoleculeMomentum : Momentum 3
  outgoingOxygenAtomMomentum : Momentum 3

/--
A dissociation is kinematically feasible at the given scalar angular-frequency readout and angle.

The frequency, momenta, masses, energies, and speed of light are all read in `workingUnits`.
The existential momenta allow this predicate to give `omegaMin` its threshold meaning without
prescribing the requested numerical value.
-/
def DissociationAt
    (s : OzonePhotodissociationSetup) (angle omega : ℝ) : Prop :=
  0 ≤ omega ∧
    ∃ photonMomentum oxygenMoleculeMomentum oxygenAtomMomentum : Momentum 3,
      photonMomentum = oxygenMoleculeMomentum + oxygenAtomMomentum ∧
      MakesAngle oxygenMoleculeMomentum photonMomentum angle ∧
      Real.sqrt (momentumSquaredNorm photonMomentum) =
        scalarInUnits reducedPlanckConstant s.workingUnits * omega /
          scalarInUnits DimSpeed.speedOfLight s.workingUnits ∧
      scalarInUnits reducedPlanckConstant s.workingUnits * omega =
        scalarInUnits s.deltaU s.workingUnits +
          momentumSquaredNorm oxygenMoleculeMomentum /
            (2 * scalarInUnits s.oxygenMoleculeMass s.workingUnits) +
          momentumSquaredNorm oxygenAtomMomentum /
            (2 * scalarInUnits s.oxygenAtomMass s.workingUnits)

/--
The governing physics used for Figure 1c.

The conservation equations encode isolation. The kinetic-energy terms are the classical,
non-relativistic expressions, while the fragment-mass equations encode that potential energies
do not contribute to mass.
-/
structure ValidOzonePhotodissociationPhysics
    (s : OzonePhotodissociationSetup) : Prop where
  angle_range : 0 ≤ s.theta ∧ s.theta ≤ Real.pi
  atomMass_pos : 0 < scalarInUnits s.atomMass s.workingUnits
  oxygenMoleculeMass_eq :
    s.oxygenMoleculeMass = (2 : ℝ≥0) • s.atomMass
  oxygenAtomMass_eq : s.oxygenAtomMass = s.atomMass
  initialOzoneAtRest : s.initialOzoneMomentum = 0
  deltaU_eq_groundEnergyDifference : ∀ u : UnitChoices,
    scalarInUnits s.deltaU u =
      scalarInUnits s.finalOxygenMoleculeGroundEnergy u -
        scalarInUnits s.initialOzoneGroundEnergy u
  photonEnergy_eq_hbarOmega : ∀ u : UnitChoices,
    scalarInUnits s.thresholdPhotonEnergy u =
      scalarInUnits reducedPlanckConstant u * scalarInUnits s.omegaMin u
  photonMomentum_eq_energy_div_c :
    Real.sqrt (momentumSquaredNorm s.incidentPhotonMomentum) =
      scalarInUnits s.thresholdPhotonEnergy s.workingUnits /
        scalarInUnits DimSpeed.speedOfLight s.workingUnits
  momentum_conservation :
    s.incidentPhotonMomentum + s.initialOzoneMomentum =
      s.outgoingOxygenMoleculeMomentum + s.outgoingOxygenAtomMomentum
  outgoingOxygenMolecule_angle :
    MakesAngle s.outgoingOxygenMoleculeMomentum
      s.incidentPhotonMomentum s.theta
  energy_conservation :
    scalarInUnits s.thresholdPhotonEnergy s.workingUnits +
        scalarInUnits s.initialOzoneGroundEnergy s.workingUnits =
      scalarInUnits s.finalOxygenMoleculeGroundEnergy s.workingUnits +
        momentumSquaredNorm s.outgoingOxygenMoleculeMomentum /
          (2 * scalarInUnits s.oxygenMoleculeMass s.workingUnits) +
        momentumSquaredNorm s.outgoingOxygenAtomMomentum /
          (2 * scalarInUnits s.oxygenAtomMass s.workingUnits)
  omegaMin_is_threshold :
    IsLeast
      {ω : ℝ | DissociationAt s s.theta ω}
      (scalarInUnits s.omegaMin s.workingUnits)

/--
The corrected threshold angular-frequency expression quoted in the blueprint from part C.1.

The factor `2` in the radicand is the conservation-law correction supplied by C.1.
-/
noncomputable def quotedC1ThresholdExpression
    (s : OzonePhotodissociationSetup) (angle : ℝ) : ℝ :=
  let angularFactor := 2 * (Real.sin angle) ^ 2 + 1
  let restEnergyScale :=
    3 * siScalar s.atomMass * (siScalar DimSpeed.speedOfLight) ^ 2
  restEnergyScale *
      (1 - Real.sqrt
        (1 -
          2 * angularFactor * siScalar s.deltaU / restEnergyScale)) /
    (siScalar reducedPlanckConstant * angularFactor)

/--
The reusable corrected C.1 conclusion supplied by the blueprint. For backward angles, the
threshold is the same corrected expression evaluated at `π/2`.
-/
structure QuotedPreviousPartC1Result
    (s : OzonePhotodissociationSetup) : Prop where
  forwardAngle : s.theta ≤ Real.pi / 2 →
    siScalar s.omegaMin = quotedC1ThresholdExpression s s.theta
  backwardAngle : Real.pi / 2 ≤ s.theta →
    siScalar s.omegaMin =
      quotedC1ThresholdExpression s (Real.pi / 2)

/-- The three scalar inputs specified in subquestion C.2, attached to their physical units. -/
structure C2NumericalInputs (s : OzonePhotodissociationSetup) : Prop where
  theta_eq : s.theta = Real.pi / 6
  deltaU_eq :
    s.deltaU = (11 / 10 : ℝ≥0) • DimEnergy.electronVolt
  atomMass_eq :
    s.atomMass = (16 : ℝ≥0) • atomicMassUnit

/--
`x` is reported as `reported` to a precision whose half-width is `tolerance`.

This makes the significant-figure meaning of a numerical physics answer explicit.
-/
def RoundsTo (x reported tolerance : ℝ) : Prop :=
  |x - reported| ≤ tolerance

/--
For `θ = π/6`, `ΔU = 1.10 eV`, and oxygen-atom mass `16.0 amu`, the threshold
excess energy `ℏ ω_min - ΔU` is `2.03 × 10⁻¹¹ eV` to the reported precision.

Blueprint label: `thm:physics:IPhO_2026_1_C_2:target`.
-/
theorem problem_IPhO_2026_1_C_2
    (s : OzonePhotodissociationSetup)
    (physics : ValidOzonePhotodissociationPhysics s)
    (previousPart : QuotedPreviousPartC1Result s)
    (data : C2NumericalInputs s) :
    RoundsTo
      ((siScalar reducedPlanckConstant * siScalar s.omegaMin -
          siScalar s.deltaU) /
        siScalar DimEnergy.electronVolt)
      2.03e-11 5e-14 := by
  rw [previousPart.forwardAngle (by
    rw [data.theta_eq]
    have := Real.pi_pos
    linarith)]
  let t : ℝ :=
    Real.sqrt 932761304735321063788707343 /
      Real.sqrt 932761304804164591030894843
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_sq :
      t ^ 2 =
        (932761304735321063788707343 : ℝ) /
          932761304804164591030894843 := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  have ht_lower :
      (999999999963096921533472 : ℝ) /
          1000000000000000000000000 ≤ t := by
    nlinarith [ht_sq]
  have ht_upper :
      t ≤
        (999999999963096921533473 : ℝ) /
          1000000000000000000000000 := by
    nlinarith [ht_sq]
  norm_num [RoundsTo, quotedC1ThresholdExpression, data.theta_eq,
    data.atomMass_eq, data.deltaU_eq, siScalar, scalarInUnits,
    reducedPlanckConstant, atomicMassUnit, DimEnergy.electronVolt,
    DimSpeed.speedOfLight, CarriesDimension.toDimensionful_apply_apply,
    Constants.ℏ, NNReal.smul_def, abs_le]
  dsimp [t] at ht_lower ht_upper
  constructor <;> nlinarith [ht_lower, ht_upper]

end IPhO2026Problems.IPhO2026_1_C_2
