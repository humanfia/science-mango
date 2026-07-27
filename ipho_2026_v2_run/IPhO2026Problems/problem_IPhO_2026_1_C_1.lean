import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Relativity.SpeedOfLight

/-!
# IPhO 2026, problem 1, part C.1

This file models the photodissociation

`γ + O₃ (at rest) → O₂ + O`

shown in Figure 1c. Numerical values are read in one fixed coherent system of
units. In particular, momenta are represented by two-dimensional real vectors,
while the names of the scalar fields record their dimensional roles.
-/

noncomputable section

namespace IPhO2026Problem1C1

/-- The two-dimensional momentum-coordinate space used for Figure 1c. -/
abbrev MomentumPlane := EuclideanSpace ℝ (Fin 2)

/-- The incident-photon direction (the horizontal dashed ray in Figure 1c). -/
def figure1cIncidentDirection : MomentumPlane :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/--
Scalar readouts for the photodissociation experiment in one coherent unit
system. The fields have dimensions `energy · time`, `mass`, `speed`, and
`energy`, respectively.

The oxygen atom's ground-state energy is the chosen zero of energy, as in the
source energy balance.
-/
structure Parameters where
  reducedPlanckConstant : ℝ
  oxygenAtomMass : ℝ
  speedOfLight : SpeedOfLight
  ozoneGroundEnergy : ℝ
  oxygenMoleculeGroundEnergy : ℝ

/-- The dissociation energy gap `ΔU = U_f - U_i`. -/
def Parameters.energyGap (parameters : Parameters) : ℝ :=
  parameters.oxygenMoleculeGroundEnergy - parameters.ozoneGroundEnergy

/--
Applicability conditions for the classical threshold formula.

The last inequality keeps the relevant discriminants strictly positive and is
the quantitative small-energy condition appropriate to the nonrelativistic
model.
-/
def Parameters.Valid (parameters : Parameters) : Prop :=
  0 < parameters.reducedPlanckConstant ∧
    0 < parameters.oxygenAtomMass ∧
    0 < parameters.energyGap ∧
    2 * parameters.energyGap <
      parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2

/-- Photon energy `E_γ = ℏω` in the chosen coherent units. -/
def photonEnergy (parameters : Parameters) (angularFrequency : ℝ) : ℝ :=
  parameters.reducedPlanckConstant * angularFrequency

/-- Photon momentum magnitude `p_γ = E_γ / c = ℏω/c`. -/
def photonMomentumMagnitude (parameters : Parameters) (angularFrequency : ℝ) : ℝ :=
  photonEnergy parameters angularFrequency / parameters.speedOfLight.val

/--
Classical, nonrelativistic kinetic energy of the outgoing fragments.

The oxygen molecule has mass `2m`, hence its term is `|p|²/(4m)`;
the oxygen atom has mass `m`, hence its term is `|q|²/(2m)`.
-/
def fragmentKineticEnergy (parameters : Parameters)
    (oxygenMoleculeMomentum oxygenAtomMomentum : MomentumPlane) : ℝ :=
  ‖oxygenMoleculeMomentum‖ ^ 2 / (4 * parameters.oxygenAtomMass) +
    ‖oxygenAtomMomentum‖ ^ 2 / (2 * parameters.oxygenAtomMass)

/--
A single event satisfying the governing laws of the isolated
photodissociation process.

The named momentum fields distinguish the incoming photon from both outgoing
fragments. The angle is Mathlib's unoriented angle in `[0, π]`, matching the
angle label `θ` in Figure 1c.
-/
structure DissociationEvent (parameters : Parameters)
    (theta angularFrequency : ℝ) where
  angularFrequency_pos : 0 < angularFrequency
  theta_nonneg : 0 ≤ theta
  theta_le_pi : theta ≤ Real.pi
  photonMomentum : MomentumPlane
  oxygenMoleculeMomentum : MomentumPlane
  oxygenAtomMomentum : MomentumPlane
  oxygenMoleculeMomentum_ne_zero : oxygenMoleculeMomentum ≠ 0
  photon_momentum_law :
    photonMomentum =
      photonMomentumMagnitude parameters angularFrequency •
        figure1cIncidentDirection
  momentum_conservation :
    photonMomentum = oxygenMoleculeMomentum + oxygenAtomMomentum
  figure1c_angle :
    InnerProductGeometry.angle photonMomentum oxygenMoleculeMomentum = theta
  energy_conservation :
    photonEnergy parameters angularFrequency + parameters.ozoneGroundEnergy =
      parameters.oxygenMoleculeGroundEnergy +
        fragmentKineticEnergy parameters oxygenMoleculeMomentum oxygenAtomMomentum

/-- Dissociation at the stated angle and frequency is kinematically possible. -/
def KinematicallyAllowed (parameters : Parameters)
    (theta angularFrequency : ℝ) : Prop :=
  Nonempty (DissociationEvent parameters theta angularFrequency)

/--
The radial form of the total fragment kinetic energy after eliminating the
oxygen-atom momentum with momentum conservation. Here `r = |p_{O₂}|`.
-/
def radialFragmentKineticEnergy (parameters : Parameters)
    (theta angularFrequency oxygenMoleculeMomentumMagnitude : ℝ) : ℝ :=
  let q := photonMomentumMagnitude parameters angularFrequency
  let r := oxygenMoleculeMomentumMagnitude
  r ^ 2 / (4 * parameters.oxygenAtomMass) +
    (q ^ 2 + r ^ 2 - 2 * q * r * Real.cos theta) /
      (2 * parameters.oxygenAtomMass)

/-- The angular factor `1 + 2 sin² θ` appearing in the threshold. -/
def angularFactor (theta : ℝ) : ℝ :=
  2 * Real.sin theta ^ 2 + 1

/--
Infimum of the radial fragment kinetic energy at fixed photon momentum.

For forward angles the minimizing oxygen-molecule momentum is nonnegative.
For angles at or beyond `π/2`, the constrained infimum occurs as that momentum
tends to zero.
-/
def minimumFragmentKineticEnergy (parameters : Parameters)
    (theta angularFrequency : ℝ) : ℝ :=
  let q := photonMomentumMagnitude parameters angularFrequency
  if theta ≤ Real.pi / 2 then
    q ^ 2 * angularFactor theta / (6 * parameters.oxygenAtomMass)
  else
    q ^ 2 / (2 * parameters.oxygenAtomMass)

/--
The exact scalar feasibility condition obtained by minimizing over the
outgoing oxygen-molecule momentum magnitude.

At and beyond `π/2` the infimum requires zero O₂ momentum, for which the angle
would not be physically defined; consequently actual events satisfy a strict
inequality there.
-/
def HasEnoughPhotonEnergy (parameters : Parameters)
    (theta angularFrequency : ℝ) : Prop :=
  if theta < Real.pi / 2 then
    parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta angularFrequency ≤
      photonEnergy parameters angularFrequency
  else
    parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta angularFrequency <
      photonEnergy parameters angularFrequency

/--
An infimum characterization of the minimum required angular frequency.

This permits the backscattering threshold to be a limiting value even when no
event with nonzero outgoing O₂ momentum occurs exactly at that value.
-/
def IsDissociationThreshold (parameters : Parameters)
    (theta threshold : ℝ) : Prop :=
  0 ≤ threshold ∧
    (∀ angularFrequency,
      KinematicallyAllowed parameters theta angularFrequency →
        threshold ≤ angularFrequency) ∧
    ∀ epsilon, 0 < epsilon →
      ∃ angularFrequency,
        KinematicallyAllowed parameters theta angularFrequency ∧
          angularFrequency < threshold + epsilon

/--
Under the parameter-validity conditions, vector conservation and the
Figure 1c angle imply the scalar energy law.
-/
theorem event_scalar_energy_balance
    {parameters : Parameters} {theta angularFrequency : ℝ}
    (hParameters : parameters.Valid)
    (event : DissociationEvent parameters theta angularFrequency) :
    photonEnergy parameters angularFrequency =
      parameters.energyGap +
        radialFragmentKineticEnergy parameters theta angularFrequency
          ‖event.oxygenMoleculeMomentum‖ := by
  have hEnergy :
      photonEnergy parameters angularFrequency =
        parameters.energyGap +
          fragmentKineticEnergy parameters event.oxygenMoleculeMomentum
            event.oxygenAtomMomentum := by
    rw [Parameters.energyGap]
    linarith [event.energy_conservation]
  rw [hEnergy]
  congr 1
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hPhotonMomentum :
      0 < photonMomentumMagnitude parameters angularFrequency := by
    unfold photonMomentumMagnitude photonEnergy
    have hSpeed : 0 < parameters.speedOfLight.val :=
      parameters.speedOfLight.pos
    exact div_pos (mul_pos hPlanck event.angularFrequency_pos) hSpeed
  have hDirectionNorm : ‖figure1cIncidentDirection‖ = 1 := by
    simp [figure1cIncidentDirection]
  have hPhotonNorm :
      ‖event.photonMomentum‖ =
        photonMomentumMagnitude parameters angularFrequency := by
    rw [event.photon_momentum_law, norm_smul, hDirectionNorm, mul_one,
      Real.norm_eq_abs, abs_of_pos hPhotonMomentum]
  have hInner :
      inner ℝ event.photonMomentum event.oxygenMoleculeMomentum =
        photonMomentumMagnitude parameters angularFrequency *
          ‖event.oxygenMoleculeMomentum‖ * Real.cos theta := by
    have hCosineLaw :=
      InnerProductGeometry.cos_angle_mul_norm_mul_norm
        event.photonMomentum event.oxygenMoleculeMomentum
    rw [event.figure1c_angle, hPhotonNorm] at hCosineLaw
    nlinarith
  have hAtomMomentum :
      event.oxygenAtomMomentum =
        event.photonMomentum - event.oxygenMoleculeMomentum := by
    exact (eq_sub_iff_add_eq').2 event.momentum_conservation.symm
  unfold fragmentKineticEnergy radialFragmentKineticEnergy
  dsimp only
  rw [hAtomMomentum, norm_sub_pow_two_real, hPhotonNorm, hInner]
  ring

/--
The constrained radial kinetic energy is bounded below by the appropriate
forward/backscattering infimum.
-/
theorem radialFragmentKineticEnergy_lower_bound
    {parameters : Parameters} {theta angularFrequency r : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hAngularFrequency : 0 ≤ angularFrequency)
    (hMomentumMagnitude : 0 ≤ r) :
    minimumFragmentKineticEnergy parameters theta angularFrequency ≤
      radialFragmentKineticEnergy parameters theta angularFrequency r := by
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hSpeed : 0 < parameters.speedOfLight.val :=
    parameters.speedOfLight.pos
  have hPhotonEnergy : 0 ≤ photonEnergy parameters angularFrequency := by
    unfold photonEnergy
    positivity
  have hPhotonMomentum :
      0 ≤ photonMomentumMagnitude parameters angularFrequency := by
    unfold photonMomentumMagnitude
    positivity
  by_cases hForward : theta ≤ Real.pi / 2
  · rw [minimumFragmentKineticEnergy, if_pos hForward]
    have hTrig := Real.sin_sq_add_cos_sq theta
    have hSquare :
        0 ≤
          (3 * r -
            2 * photonMomentumMagnitude parameters angularFrequency *
              Real.cos theta) ^ 2 := sq_nonneg _
    have hMinimum :
        photonMomentumMagnitude parameters angularFrequency ^ 2 *
              angularFactor theta /
            (6 * parameters.oxygenAtomMass) =
          (2 * photonMomentumMagnitude parameters angularFrequency ^ 2 *
              angularFactor theta) /
            (12 * parameters.oxygenAtomMass) := by
      field_simp
      ring
    have hRadial :
        radialFragmentKineticEnergy parameters theta angularFrequency r =
          (3 * r ^ 2 +
              6 * (photonMomentumMagnitude parameters angularFrequency ^ 2 +
                r ^ 2 -
                2 * photonMomentumMagnitude parameters angularFrequency * r *
                  Real.cos theta)) /
            (12 * parameters.oxygenAtomMass) := by
      unfold radialFragmentKineticEnergy
      dsimp only
      field_simp
      ring
    rw [hMinimum, hRadial]
    apply (div_le_div_iff_of_pos_right (by positivity :
      0 < 12 * parameters.oxygenAtomMass)).2
    unfold angularFactor
    nlinarith
  · rw [minimumFragmentKineticEnergy, if_neg hForward]
    have hHalfPi : Real.pi / 2 ≤ theta := le_of_not_ge hForward
    have hCos :
        Real.cos theta ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hHalfPi
        (by nlinarith [Real.pi_pos])
    have hMinimum :
        photonMomentumMagnitude parameters angularFrequency ^ 2 /
            (2 * parameters.oxygenAtomMass) =
          (2 * photonMomentumMagnitude parameters angularFrequency ^ 2) /
            (4 * parameters.oxygenAtomMass) := by
      field_simp
      ring
    have hRadial :
        radialFragmentKineticEnergy parameters theta angularFrequency r =
          (r ^ 2 +
              2 * (photonMomentumMagnitude parameters angularFrequency ^ 2 +
                r ^ 2 -
                2 * photonMomentumMagnitude parameters angularFrequency * r *
                  Real.cos theta)) /
            (4 * parameters.oxygenAtomMass) := by
      unfold radialFragmentKineticEnergy
      dsimp only
      field_simp
      ring
    rw [hMinimum, hRadial]
    apply (div_le_div_iff_of_pos_right (by positivity :
      0 < 4 * parameters.oxygenAtomMass)).2
    have hCross :
        0 ≤
          -4 * photonMomentumMagnitude parameters angularFrequency * r *
            Real.cos theta := by
      have h :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hPhotonMomentum)
            hMomentumMagnitude)
          (neg_nonneg.mpr hCos)
      nlinarith
    nlinarith [sq_nonneg r]

/--
The vector event interface is neither opaque nor underdetermined: eliminating
the two momentum vectors gives exactly the scalar minimized-energy condition.
-/
theorem kinematicallyAllowed_iff_hasEnoughPhotonEnergy
    {parameters : Parameters} {theta angularFrequency : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hAngularFrequency : 0 < angularFrequency) :
    KinematicallyAllowed parameters theta angularFrequency ↔
      HasEnoughPhotonEnergy parameters theta angularFrequency := by
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hSpeed : 0 < parameters.speedOfLight.val :=
    parameters.speedOfLight.pos
  have hPhotonMomentum :
      0 < photonMomentumMagnitude parameters angularFrequency := by
    unfold photonMomentumMagnitude photonEnergy
    positivity
  constructor
  · rintro ⟨event⟩
    have hDirectionNorm : ‖figure1cIncidentDirection‖ = 1 := by
      simp [figure1cIncidentDirection]
    have hPhotonNorm :
        ‖event.photonMomentum‖ =
          photonMomentumMagnitude parameters angularFrequency := by
      rw [event.photon_momentum_law, norm_smul, hDirectionNorm, mul_one,
        Real.norm_eq_abs, abs_of_pos hPhotonMomentum]
    have hInner :
        inner ℝ event.photonMomentum event.oxygenMoleculeMomentum =
          photonMomentumMagnitude parameters angularFrequency *
            ‖event.oxygenMoleculeMomentum‖ * Real.cos theta := by
      have hCosineLaw :=
        InnerProductGeometry.cos_angle_mul_norm_mul_norm
          event.photonMomentum event.oxygenMoleculeMomentum
      rw [event.figure1c_angle, hPhotonNorm] at hCosineLaw
      nlinarith
    have hAtomMomentum :
        event.oxygenAtomMomentum =
          event.photonMomentum - event.oxygenMoleculeMomentum := by
      exact (eq_sub_iff_add_eq').2 event.momentum_conservation.symm
    have hFragmentRadial :
        fragmentKineticEnergy parameters event.oxygenMoleculeMomentum
            event.oxygenAtomMomentum =
          radialFragmentKineticEnergy parameters theta angularFrequency
            ‖event.oxygenMoleculeMomentum‖ := by
      unfold fragmentKineticEnergy radialFragmentKineticEnergy
      dsimp only
      rw [hAtomMomentum, norm_sub_pow_two_real, hPhotonNorm, hInner]
      ring
    have hBalance :
        photonEnergy parameters angularFrequency =
          parameters.energyGap +
            radialFragmentKineticEnergy parameters theta angularFrequency
              ‖event.oxygenMoleculeMomentum‖ := by
      rw [← hFragmentRadial]
      unfold Parameters.energyGap
      linarith [event.energy_conservation]
    by_cases hAcute : theta < Real.pi / 2
    · rw [HasEnoughPhotonEnergy, if_pos hAcute]
      have hLower :=
        radialFragmentKineticEnergy_lower_bound
          ⟨hPlanck, hMass, hGap, hSmall⟩ hThetaNonnegative hThetaAtMostPi
          hAngularFrequency.le (norm_nonneg event.oxygenMoleculeMomentum)
      linarith
    · rw [HasEnoughPhotonEnergy, if_neg hAcute]
      have hHalfPi : Real.pi / 2 ≤ theta := le_of_not_gt hAcute
      have hCos :
          Real.cos theta ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hHalfPi
          (by nlinarith [Real.pi_pos])
      have hMomentumNorm : 0 < ‖event.oxygenMoleculeMomentum‖ :=
        norm_pos_iff.mpr event.oxygenMoleculeMomentum_ne_zero
      have hMinimum :
          minimumFragmentKineticEnergy parameters theta angularFrequency =
            photonMomentumMagnitude parameters angularFrequency ^ 2 /
              (2 * parameters.oxygenAtomMass) := by
        by_cases hAtMostHalfPi : theta ≤ Real.pi / 2
        · have hThetaEq : theta = Real.pi / 2 := le_antisymm hAtMostHalfPi hHalfPi
          subst theta
          norm_num [minimumFragmentKineticEnergy, angularFactor]
          field_simp
          ring
        · rw [minimumFragmentKineticEnergy, if_neg hAtMostHalfPi]
      have hRadial :
          radialFragmentKineticEnergy parameters theta angularFrequency
              ‖event.oxygenMoleculeMomentum‖ =
            (‖event.oxygenMoleculeMomentum‖ ^ 2 +
                2 *
                  (photonMomentumMagnitude parameters angularFrequency ^ 2 +
                    ‖event.oxygenMoleculeMomentum‖ ^ 2 -
                    2 * photonMomentumMagnitude parameters angularFrequency *
                      ‖event.oxygenMoleculeMomentum‖ * Real.cos theta)) /
              (4 * parameters.oxygenAtomMass) := by
        unfold radialFragmentKineticEnergy
        dsimp only
        field_simp
        ring
      have hCross :
          0 ≤
            -4 * photonMomentumMagnitude parameters angularFrequency *
              ‖event.oxygenMoleculeMomentum‖ * Real.cos theta := by
        have h :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
                hPhotonMomentum.le)
              hMomentumNorm.le)
            (neg_nonneg.mpr hCos)
        nlinarith
      have hStrict :
          minimumFragmentKineticEnergy parameters theta angularFrequency <
            radialFragmentKineticEnergy parameters theta angularFrequency
              ‖event.oxygenMoleculeMomentum‖ := by
        rw [hMinimum, hRadial]
        rw [show
          photonMomentumMagnitude parameters angularFrequency ^ 2 /
                (2 * parameters.oxygenAtomMass) =
              (2 * photonMomentumMagnitude parameters angularFrequency ^ 2) /
                (4 * parameters.oxygenAtomMass) by
            field_simp
            ring]
        rw [div_lt_div_iff_of_pos_right (by positivity :
          0 < 4 * parameters.oxygenAtomMass)]
        nlinarith [sq_pos_of_pos hMomentumNorm]
      linarith
  · intro hEnough
    let q := photonMomentumMagnitude parameters angularFrequency
    let availableEnergy :=
      photonEnergy parameters angularFrequency - parameters.energyGap
    let discriminant :=
      (4 * q * Real.cos theta) ^ 2 -
        12 * (2 * q ^ 2 - 4 * parameters.oxygenAtomMass * availableEnergy)
    let radius :=
      (4 * q * Real.cos theta + Real.sqrt discriminant) / 6
    have hQ : 0 < q := by
      dsimp [q]
      exact hPhotonMomentum
    have hDiscriminantAndRadius :
        0 ≤ discriminant ∧ 0 < radius := by
      by_cases hAcute : theta < Real.pi / 2
      · rw [HasEnoughPhotonEnergy, if_pos hAcute] at hEnough
        rw [minimumFragmentKineticEnergy, if_pos hAcute.le] at hEnough
        have hBound :
            q ^ 2 * angularFactor theta /
                  (6 * parameters.oxygenAtomMass) ≤
                availableEnergy := by
          dsimp [q, availableEnergy] at hEnough ⊢
          linarith
        have hScaled :
            q ^ 2 * angularFactor theta ≤
              6 * parameters.oxygenAtomMass * availableEnergy := by
          have h :=
            (div_le_iff₀ (by positivity :
              0 < 6 * parameters.oxygenAtomMass)).1 hBound
          nlinarith
        have hTrig := Real.sin_sq_add_cos_sq theta
        have hDiscriminant : 0 ≤ discriminant := by
          dsimp [discriminant, angularFactor] at *
          nlinarith
        have hCosPositive : 0 < Real.cos theta := by
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · nlinarith [Real.pi_pos]
          · exact hAcute
        have hRadius : 0 < radius := by
          dsimp [radius]
          have hSqrt := Real.sqrt_nonneg discriminant
          positivity
        exact ⟨hDiscriminant, hRadius⟩
      · rw [HasEnoughPhotonEnergy, if_neg hAcute] at hEnough
        have hHalfPi : Real.pi / 2 ≤ theta := le_of_not_gt hAcute
        have hMinimum :
            minimumFragmentKineticEnergy parameters theta angularFrequency =
              q ^ 2 / (2 * parameters.oxygenAtomMass) := by
          by_cases hAtMostHalfPi : theta ≤ Real.pi / 2
          · have hThetaEq : theta = Real.pi / 2 :=
              le_antisymm hAtMostHalfPi hHalfPi
            subst theta
            dsimp [q]
            norm_num [minimumFragmentKineticEnergy, angularFactor]
            field_simp
            ring
          · rw [minimumFragmentKineticEnergy, if_neg hAtMostHalfPi]
        rw [hMinimum] at hEnough
        have hBound :
            q ^ 2 / (2 * parameters.oxygenAtomMass) < availableEnergy := by
          dsimp [availableEnergy]
          linarith
        have hScaled :
            q ^ 2 < 2 * parameters.oxygenAtomMass * availableEnergy := by
          have h :=
            (div_lt_iff₀ (by positivity :
              0 < 2 * parameters.oxygenAtomMass)).1 hBound
          simpa [mul_comm] using h
        have hDiscriminantStrict :
            (4 * q * Real.cos theta) ^ 2 < discriminant := by
          dsimp [discriminant]
          nlinarith
        have hDiscriminant : 0 ≤ discriminant := by
          have hSquare : 0 ≤ (4 * q * Real.cos theta) ^ 2 := sq_nonneg _
          linarith
        have hCos :
            Real.cos theta ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le hHalfPi
            (by nlinarith [Real.pi_pos])
        have hSquareRoot := Real.sq_sqrt hDiscriminant
        have hSquareRootLarge :
            -4 * q * Real.cos theta < Real.sqrt discriminant := by
          have hLeftNonnegative : 0 ≤ -4 * q * Real.cos theta := by
            have h :=
              mul_nonneg
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hQ.le)
                (neg_nonneg.mpr hCos)
            nlinarith
          have hSqrtNonnegative := Real.sqrt_nonneg discriminant
          nlinarith
        have hRadius : 0 < radius := by
          dsimp [radius]
          nlinarith
        exact ⟨hDiscriminant, hRadius⟩
    rcases hDiscriminantAndRadius with ⟨hDiscriminant, hRadius⟩
    have hSquareRoot := Real.sq_sqrt hDiscriminant
    have hQuadratic :
        3 * radius ^ 2 - 4 * q * Real.cos theta * radius +
            2 * q ^ 2 -
            4 * parameters.oxygenAtomMass * availableEnergy =
          0 := by
      dsimp [radius, discriminant] at hSquareRoot ⊢
      nlinarith
    have hRadialEnergy :
        radialFragmentKineticEnergy parameters theta angularFrequency radius =
          availableEnergy := by
      unfold radialFragmentKineticEnergy
      dsimp only
      change
        radius ^ 2 / (4 * parameters.oxygenAtomMass) +
            (q ^ 2 + radius ^ 2 -
                2 * q * radius * Real.cos theta) /
              (2 * parameters.oxygenAtomMass) =
          availableEnergy
      field_simp
      nlinarith
    let perpendicularDirection : MomentumPlane :=
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    let photonVector : MomentumPlane :=
      q • figure1cIncidentDirection
    let moleculeVector : MomentumPlane :=
      (radius * Real.cos theta) • figure1cIncidentDirection +
        (radius * Real.sin theta) • perpendicularDirection
    let atomVector : MomentumPlane := photonVector - moleculeVector
    have hDirectionNorm : ‖figure1cIncidentDirection‖ = 1 := by
      simp [figure1cIncidentDirection]
    have hPerpendicularNorm : ‖perpendicularDirection‖ = 1 := by
      simp [perpendicularDirection]
    have hOrthogonal :
        inner ℝ figure1cIncidentDirection perpendicularDirection = 0 := by
      simp only [figure1cIncidentDirection, perpendicularDirection]
      rw [EuclideanSpace.inner_single_left]
      norm_num [EuclideanSpace.single_apply]
    have hOrthogonal' :
        inner ℝ perpendicularDirection figure1cIncidentDirection = 0 := by
      rw [real_inner_comm]
      exact hOrthogonal
    have hDirectionSelf :
        inner ℝ figure1cIncidentDirection figure1cIncidentDirection = 1 := by
      rw [real_inner_self_eq_norm_sq, hDirectionNorm]
      norm_num
    have hPerpendicularSelf :
        inner ℝ perpendicularDirection perpendicularDirection = 1 := by
      rw [real_inner_self_eq_norm_sq, hPerpendicularNorm]
      norm_num
    have hMoleculeNormSquared : ‖moleculeVector‖ ^ 2 = radius ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      dsimp [moleculeVector]
      simp only [inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right]
      rw [hDirectionSelf, hOrthogonal, hOrthogonal', hPerpendicularSelf]
      norm_num
      calc
        radius * Real.cos theta * (radius * Real.cos theta) +
              radius * Real.sin theta * (radius * Real.sin theta) =
            radius ^ 2 *
              (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
        _ = radius ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hMoleculeNorm : ‖moleculeVector‖ = radius := by
      exact
        (sq_eq_sq₀ (norm_nonneg moleculeVector) hRadius.le).mp
          hMoleculeNormSquared
    have hMoleculeNonzero : moleculeVector ≠ 0 := by
      apply norm_pos_iff.mp
      simpa only [hMoleculeNorm] using hRadius
    have hPhotonNorm : ‖photonVector‖ = q := by
      dsimp [photonVector]
      rw [norm_smul, hDirectionNorm, mul_one, Real.norm_eq_abs,
        abs_of_pos hQ]
    have hInner :
        inner ℝ photonVector moleculeVector =
          q * radius * Real.cos theta := by
      dsimp [photonVector, moleculeVector]
      simp only [inner_add_right, inner_smul_left, inner_smul_right]
      rw [hDirectionSelf, hOrthogonal]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have hAngle : InnerProductGeometry.angle photonVector moleculeVector = theta := by
      have hCosineLaw :=
        InnerProductGeometry.cos_angle_mul_norm_mul_norm
          photonVector moleculeVector
      rw [hPhotonNorm, hMoleculeNorm, hInner] at hCosineLaw
      have hCosine :
          Real.cos (InnerProductGeometry.angle photonVector moleculeVector) =
            Real.cos theta := by
        have hProductPositive : 0 < q * radius := mul_pos hQ hRadius
        apply mul_right_cancel₀ hProductPositive.ne'
        calc
          Real.cos (InnerProductGeometry.angle photonVector moleculeVector) *
                (q * radius) =
              q * radius * Real.cos theta := hCosineLaw
          _ = Real.cos theta * (q * radius) := by ring
      exact
        Real.strictAntiOn_cos.injOn
          ⟨InnerProductGeometry.angle_nonneg _ _,
            InnerProductGeometry.angle_le_pi _ _⟩
          ⟨hThetaNonnegative, hThetaAtMostPi⟩ hCosine
    have hFragmentEnergy :
        fragmentKineticEnergy parameters moleculeVector atomVector =
          availableEnergy := by
      unfold fragmentKineticEnergy
      dsimp [atomVector]
      rw [hMoleculeNorm, norm_sub_pow_two_real, hPhotonNorm,
        hMoleculeNorm, hInner]
      unfold radialFragmentKineticEnergy at hRadialEnergy
      dsimp only at hRadialEnergy
      change
        radius ^ 2 / (4 * parameters.oxygenAtomMass) +
            (q ^ 2 - 2 * (q * radius * Real.cos theta) + radius ^ 2) /
              (2 * parameters.oxygenAtomMass) =
          availableEnergy
      convert hRadialEnergy using 1 <;> ring
    refine ⟨{
      angularFrequency_pos := hAngularFrequency
      theta_nonneg := hThetaNonnegative
      theta_le_pi := hThetaAtMostPi
      photonMomentum := photonVector
      oxygenMoleculeMomentum := moleculeVector
      oxygenAtomMomentum := atomVector
      oxygenMoleculeMomentum_ne_zero := hMoleculeNonzero
      photon_momentum_law := ?_
      momentum_conservation := ?_
      figure1c_angle := hAngle
      energy_conservation := ?_
    }⟩
    · dsimp [photonVector, q]
    · dsimp [atomVector]
      abel
    · rw [hFragmentEnergy]
      dsimp [availableEnergy, Parameters.energyGap]
      ring

/-- Clamp the Figure 1c angle to the forward limiting value `π/2`. -/
def effectiveThresholdAngle (theta : ℝ) : ℝ :=
  if theta ≤ Real.pi / 2 then theta else Real.pi / 2

/--
The threshold expression obtained from the lower root of the energy quadratic.

The factor `2` multiplying `ΔU` under the square root is present in the
official solution and is also required by the numerical result in part C.2.
The generated blueprint's recorded-answer line omitted this factor.
-/
def minimumAngularFrequencyExpression
    (parameters : Parameters) (theta : ℝ) : ℝ :=
  let effectiveTheta := effectiveThresholdAngle theta
  let factor := angularFactor effectiveTheta
  let massEnergy :=
    parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2
  3 * massEnergy *
      (1 - Real.sqrt
        (1 - (2 * parameters.energyGap / (3 * massEnergy)) * factor)) /
    (parameters.reducedPlanckConstant * factor)

/-- The displayed expression is the lower root of the minimized energy equation. -/
theorem minimumAngularFrequencyExpression_energy_boundary
    {parameters : Parameters} {theta : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi) :
    photonEnergy parameters (minimumAngularFrequencyExpression parameters theta) =
      parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta
          (minimumAngularFrequencyExpression parameters theta) := by
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hSpeed : 0 < parameters.speedOfLight.val :=
    parameters.speedOfLight.pos
  by_cases hForward : theta ≤ Real.pi / 2
  · simp only [minimumAngularFrequencyExpression, effectiveThresholdAngle,
      if_pos hForward, minimumFragmentKineticEnergy]
    have hFactorPositive : 0 < angularFactor theta := by
      unfold angularFactor
      positivity
    have hFactorAtMostThree : angularFactor theta ≤ 3 := by
      unfold angularFactor
      nlinarith [Real.sin_sq_le_one theta]
    have hMassEnergy :
        0 < parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2 := by
      positivity
    have hNumerator :
        2 * parameters.energyGap * angularFactor theta <
          3 * (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) := by
      have hFirst :
          2 * parameters.energyGap * angularFactor theta <
            (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) *
              angularFactor theta :=
        mul_lt_mul_of_pos_right hSmall hFactorPositive
      have hSecond :
          (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) *
              angularFactor theta ≤
            (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) * 3 :=
        mul_le_mul_of_nonneg_left hFactorAtMostThree hMassEnergy.le
      nlinarith
    have hDiscriminant :
        0 ≤
          1 -
            2 * parameters.energyGap /
                (3 *
                  (parameters.oxygenAtomMass *
                    parameters.speedOfLight.val ^ 2)) *
              angularFactor theta := by
      have hDenominator :
          0 <
            3 *
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) := by
        positivity
      have hTerm :
          2 * parameters.energyGap /
                (3 *
                  (parameters.oxygenAtomMass *
                    parameters.speedOfLight.val ^ 2)) *
              angularFactor theta <
            1 := by
        rw [div_mul_eq_mul_div, div_lt_one hDenominator]
        exact hNumerator
      linarith
    have hSquare := Real.sq_sqrt hDiscriminant
    simp only [photonMomentumMagnitude, photonEnergy]
    field_simp at hSquare ⊢
    nlinarith
  · simp only [minimumAngularFrequencyExpression, effectiveThresholdAngle,
      if_neg hForward, minimumFragmentKineticEnergy]
    norm_num [angularFactor]
    have hMassEnergy :
        0 < parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2 := by
      positivity
    have hDiscriminant :
        0 ≤
          1 -
            2 * parameters.energyGap /
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) := by
      have hRatio :
          2 * parameters.energyGap /
                (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) <
            1 :=
        (div_lt_one hMassEnergy).2 hSmall
      linarith
    have hSquare := Real.sq_sqrt hDiscriminant
    simp only [photonMomentumMagnitude, photonEnergy]
    field_simp at hSquare ⊢
    nlinarith

/-- An infimum threshold, when it exists, is unique. -/
theorem isDissociationThreshold_unique
    {parameters : Parameters} {theta threshold₁ threshold₂ : ℝ}
    (hThreshold₁ :
      IsDissociationThreshold parameters theta threshold₁)
    (hThreshold₂ :
      IsDissociationThreshold parameters theta threshold₂) :
    threshold₁ = threshold₂ := by
  rcases hThreshold₁ with ⟨h₁Nonnegative, h₁Lower, h₁Approached⟩
  rcases hThreshold₂ with ⟨h₂Nonnegative, h₂Lower, h₂Approached⟩
  apply le_antisymm
  · by_contra hNot
    have hStrict : threshold₂ < threshold₁ := lt_of_not_ge hNot
    obtain ⟨angularFrequency, hAllowed, hClose⟩ :=
      h₂Approached ((threshold₁ - threshold₂) / 2) (by linarith)
    have hLower := h₁Lower angularFrequency hAllowed
    linarith
  · by_contra hNot
    have hStrict : threshold₁ < threshold₂ := lt_of_not_ge hNot
    obtain ⟨angularFrequency, hAllowed, hClose⟩ :=
      h₁Approached ((threshold₂ - threshold₁) / 2) (by linarith)
    have hLower := h₂Lower angularFrequency hAllowed
    linarith

/--
Physics formalization target for
`thm:physics:IPhO_2026_1_C_1:target`.

The explicit formula itself is proved to be the minimum required angular
frequency; no threshold formula is assumed as a governing law.
-/
theorem minimumAngularFrequency_isDissociationThreshold
    (parameters : Parameters) (theta : ℝ)
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi) :
    IsDissociationThreshold parameters theta
      (minimumAngularFrequencyExpression parameters theta) := by
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hSpeed : 0 < parameters.speedOfLight.val :=
    parameters.speedOfLight.pos
  let factor := angularFactor (effectiveThresholdAngle theta)
  let massEnergy :=
    parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2
  let coefficient := factor / (6 * massEnergy)
  let threshold := minimumAngularFrequencyExpression parameters theta
  let boundaryEnergy := photonEnergy parameters threshold
  have hMassEnergy : 0 < massEnergy := by
    dsimp [massEnergy]
    positivity
  have hFactorPositive : 0 < factor := by
    dsimp [factor, effectiveThresholdAngle, angularFactor]
    split
    · positivity
    · positivity
  have hCoefficient : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  have hMinimumFormula (angularFrequency : ℝ) :
      minimumFragmentKineticEnergy parameters theta angularFrequency =
        coefficient * photonEnergy parameters angularFrequency ^ 2 := by
    by_cases hForward : theta ≤ Real.pi / 2
    · simp only [minimumFragmentKineticEnergy, if_pos hForward]
      dsimp [coefficient, factor, massEnergy, effectiveThresholdAngle]
      rw [if_pos hForward]
      unfold photonMomentumMagnitude photonEnergy
      field_simp
    · simp only [minimumFragmentKineticEnergy, if_neg hForward]
      dsimp [coefficient, factor, massEnergy, effectiveThresholdAngle]
      rw [if_neg hForward]
      norm_num [angularFactor]
      unfold photonMomentumMagnitude photonEnergy
      field_simp
      ring
  have hBoundary :
      boundaryEnergy =
        parameters.energyGap + coefficient * boundaryEnergy ^ 2 := by
    have h :=
      minimumAngularFrequencyExpression_energy_boundary
        (parameters := parameters) (theta := theta)
        ⟨hPlanck, hMass, hGap, hSmall⟩ hThetaNonnegative hThetaAtMostPi
    rw [hMinimumFormula] at h
    exact h
  have hBoundaryEnergyPositive : 0 < boundaryEnergy := by
    have hKinetic : 0 ≤ coefficient * boundaryEnergy ^ 2 := by positivity
    linarith
  have hThresholdPositive : 0 < threshold := by
    dsimp [boundaryEnergy, photonEnergy] at hBoundaryEnergyPositive
    exact pos_of_mul_pos_right hBoundaryEnergyPositive hPlanck.le
  have hMargin : 0 < 1 - 2 * coefficient * boundaryEnergy := by
    /-
    This is the positive derivative of the feasibility quadratic at the
    displayed lower root.  It follows by simplifying the explicit root and
    using strict positivity of its discriminant.
    -/
    by_cases hForward : theta ≤ Real.pi / 2
    · dsimp [coefficient, factor, massEnergy, boundaryEnergy, threshold,
        photonEnergy, minimumAngularFrequencyExpression,
        effectiveThresholdAngle]
      rw [if_pos hForward]
      have hAngularFactorPositive : 0 < angularFactor theta := by
        unfold angularFactor
        positivity
      have hFactorAtMostThree : angularFactor theta ≤ 3 := by
        unfold angularFactor
        nlinarith [Real.sin_sq_le_one theta]
      have hNumerator :
          2 * parameters.energyGap * angularFactor theta <
            3 *
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) := by
        have hFirst :
            2 * parameters.energyGap * angularFactor theta <
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) *
                angularFactor theta :=
          mul_lt_mul_of_pos_right hSmall (by
            exact hAngularFactorPositive)
        have hSecond :
            (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) *
                angularFactor theta ≤
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) *
                3 :=
          mul_le_mul_of_nonneg_left hFactorAtMostThree (by positivity)
        nlinarith
      have hDenominator :
          0 <
            3 *
              (parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2) := by
        positivity
      have hDiscriminant :
          0 <
            1 -
              2 * parameters.energyGap /
                  (3 *
                    (parameters.oxygenAtomMass *
                      parameters.speedOfLight.val ^ 2)) *
                angularFactor theta := by
        have hTerm :
            2 * parameters.energyGap /
                  (3 *
                    (parameters.oxygenAtomMass *
                      parameters.speedOfLight.val ^ 2)) *
                angularFactor theta <
              1 := by
          rw [div_mul_eq_mul_div, div_lt_one hDenominator]
          exact hNumerator
        linarith
      have hSquareRoot :
          0 <
            Real.sqrt
              (1 -
                2 * parameters.energyGap /
                    (3 *
                      (parameters.oxygenAtomMass *
                        parameters.speedOfLight.val ^ 2)) *
                  angularFactor theta) :=
        Real.sqrt_pos.2 hDiscriminant
      field_simp [hAngularFactorPositive.ne'] at hSquareRoot ⊢
      nlinarith
    · dsimp [coefficient, factor, massEnergy, boundaryEnergy, threshold,
        photonEnergy, minimumAngularFrequencyExpression,
        effectiveThresholdAngle]
      rw [if_neg hForward]
      norm_num [angularFactor]
      have hMassEnergy' :
          0 <
            parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2 := by
        positivity
      have hDiscriminant :
          0 <
            1 -
              2 * parameters.energyGap /
                (parameters.oxygenAtomMass *
                  parameters.speedOfLight.val ^ 2) := by
        have hTerm :
            2 * parameters.energyGap /
                  (parameters.oxygenAtomMass *
                    parameters.speedOfLight.val ^ 2) <
              1 :=
          (div_lt_one hMassEnergy').2 hSmall
        linarith
      have hSquareRoot :
          0 <
            Real.sqrt
              (1 -
                2 * parameters.energyGap /
                  (parameters.oxygenAtomMass *
                    parameters.speedOfLight.val ^ 2)) :=
        Real.sqrt_pos.2 hDiscriminant
      field_simp at hSquareRoot ⊢
      nlinarith
  have hFactorIdentity (energy : ℝ) :
      parameters.energyGap + coefficient * energy ^ 2 - energy =
        (energy - boundaryEnergy) *
          (coefficient * (energy + boundaryEnergy) - 1) := by
    have hZero :
        parameters.energyGap + coefficient * boundaryEnergy ^ 2 -
            boundaryEnergy =
          0 := by
      linarith [hBoundary]
    calc
      parameters.energyGap + coefficient * energy ^ 2 - energy =
          (parameters.energyGap + coefficient * boundaryEnergy ^ 2 -
              boundaryEnergy) +
            (coefficient * (energy ^ 2 - boundaryEnergy ^ 2) -
              (energy - boundaryEnergy)) := by ring
      _ = coefficient * (energy ^ 2 - boundaryEnergy ^ 2) -
            (energy - boundaryEnergy) := by rw [hZero, zero_add]
      _ = (energy - boundaryEnergy) *
            (coefficient * (energy + boundaryEnergy) - 1) := by ring
  refine ⟨hThresholdPositive.le, ?_, ?_⟩
  · intro angularFrequency hAllowed
    obtain ⟨event⟩ := hAllowed
    have hEnough :=
      (kinematicallyAllowed_iff_hasEnoughPhotonEnergy
        (parameters := parameters) (theta := theta)
        (angularFrequency := angularFrequency)
        ⟨hPlanck, hMass, hGap, hSmall⟩ hThetaNonnegative hThetaAtMostPi
        event.angularFrequency_pos).mp ⟨event⟩
    have hScalar :
        parameters.energyGap +
              coefficient * photonEnergy parameters angularFrequency ^ 2 ≤
            photonEnergy parameters angularFrequency := by
      rw [HasEnoughPhotonEnergy] at hEnough
      split at hEnough
      · simpa only [hMinimumFormula] using hEnough
      · have hStrict :
            parameters.energyGap +
                  coefficient * photonEnergy parameters angularFrequency ^ 2 <
                photonEnergy parameters angularFrequency := by
          simpa only [hMinimumFormula] using hEnough
        exact hStrict.le
    by_contra hNot
    have hFrequencyLess : angularFrequency < threshold := lt_of_not_ge hNot
    have hEnergyLess :
        photonEnergy parameters angularFrequency < boundaryEnergy := by
      dsimp [boundaryEnergy, photonEnergy]
      exact mul_lt_mul_of_pos_left hFrequencyLess hPlanck
    have hSecondNegative :
        coefficient *
              (photonEnergy parameters angularFrequency + boundaryEnergy) -
            1 <
          0 := by
      nlinarith [hMargin]
    have hProductPositive :
        0 <
          (photonEnergy parameters angularFrequency - boundaryEnergy) *
            (coefficient *
                (photonEnergy parameters angularFrequency + boundaryEnergy) -
              1) :=
      mul_pos_of_neg_of_neg (by linarith) hSecondNegative
    rw [← hFactorIdentity] at hProductPositive
    linarith
  · intro epsilon hEpsilon
    let delta :=
      min (epsilon / 2)
        ((1 - 2 * coefficient * boundaryEnergy) /
          (2 * coefficient * parameters.reducedPlanckConstant))
    have hDeltaPositive : 0 < delta := by
      dsimp [delta]
      apply lt_min
      · linarith
      · positivity
    have hDeltaLess : delta < epsilon := by
      have hDeltaLe : delta ≤ epsilon / 2 := min_le_left _ _
      linarith
    let angularFrequency := threshold + delta
    have hAngularFrequency : 0 < angularFrequency := by
      dsimp [angularFrequency]
      linarith
    have hEnergyDifference :
        photonEnergy parameters angularFrequency - boundaryEnergy =
          parameters.reducedPlanckConstant * delta := by
      dsimp [angularFrequency, boundaryEnergy, threshold, photonEnergy]
      ring
    have hDeltaBound :
        delta ≤
          (1 - 2 * coefficient * boundaryEnergy) /
            (2 * coefficient * parameters.reducedPlanckConstant) :=
      min_le_right _ _
    have hSecondNegative :
        coefficient *
              (photonEnergy parameters angularFrequency + boundaryEnergy) -
            1 <
          0 := by
      have hScaled :
          coefficient * parameters.reducedPlanckConstant * delta ≤
            (1 - 2 * coefficient * boundaryEnergy) / 2 := by
        have hRaw :=
          (le_div_iff₀ (by positivity :
            0 < 2 * coefficient * parameters.reducedPlanckConstant)).1
            hDeltaBound
        nlinarith
      nlinarith
    have hProductNegative :
        (photonEnergy parameters angularFrequency - boundaryEnergy) *
              (coefficient *
                  (photonEnergy parameters angularFrequency + boundaryEnergy) -
                1) <
            0 :=
      mul_neg_of_pos_of_neg
        (by rw [hEnergyDifference]; positivity) hSecondNegative
    rw [← hFactorIdentity] at hProductNegative
    have hEnough :
        HasEnoughPhotonEnergy parameters theta angularFrequency := by
      rw [HasEnoughPhotonEnergy]
      split
      · rw [hMinimumFormula]
        linarith
      · rw [hMinimumFormula]
        linarith
    have hAllowed :
        KinematicallyAllowed parameters theta angularFrequency :=
      (kinematicallyAllowed_iff_hasEnoughPhotonEnergy
        (parameters := parameters) (theta := theta)
        (angularFrequency := angularFrequency)
        ⟨hPlanck, hMass, hGap, hSmall⟩ hThetaNonnegative hThetaAtMostPi
        hAngularFrequency).mpr hEnough
    exact ⟨angularFrequency, hAllowed, by
      dsimp [angularFrequency]
      linarith⟩

/--
Equivalent value form: any scalar already identified semantically as the
minimum dissociation frequency equals the explicit expression.
-/
theorem minimumAngularFrequency_eq
    (parameters : Parameters) (theta omegaMinimum : ℝ)
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hMinimum :
      IsDissociationThreshold parameters theta omegaMinimum) :
    omegaMinimum = minimumAngularFrequencyExpression parameters theta := by
  exact isDissociationThreshold_unique hMinimum
    (minimumAngularFrequency_isDissociationThreshold parameters theta
      hParameters hThetaNonnegative hThetaAtMostPi)

end IPhO2026Problem1C1
