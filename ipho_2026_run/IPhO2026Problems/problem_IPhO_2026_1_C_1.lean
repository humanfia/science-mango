import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/-!
# IPhO 2026, problem 1, part C.1

A photon photodissociates an ozone molecule initially at rest into an oxygen
molecule and an oxygen atom.  This file models the SI readouts of the
dimensionful parameters, the geometry shown in Figure 1c, conservation of
momentum and energy, and the claimed piecewise minimum-frequency formula.
-/

namespace IPhO2026Problems.IPhO2026_1_C_1

open Dimension

/-- The dimensionful mass of one oxygen atom. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-- A dimensionful action, used for the reduced Planck constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) ℝ)

/-- A dimensionful angular frequency. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A dimensionful two-dimensional momentum used for Figure 1c. -/
abbrev MomentumQuantity2 : Type :=
  Dimensionful (Momentum 2)

/-- The real scalar readout of a dimensionful scalar quantity in SI units. -/
noncomputable def scalarSI {d : Dimension}
    (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q UnitChoices.SI).val

/-- The real speed readout in metres per second. -/
noncomputable def speedSI (v : DimSpeed) : ℝ :=
  ((v UnitChoices.SI).val : ℝ)

/-- The two Cartesian momentum components in SI units. -/
noncomputable def momentumSI (p : MomentumQuantity2) : Fin 2 → ℝ :=
  (p UnitChoices.SI).val

/-- Euclidean dot product of the two displayed momentum vectors. -/
def dot2 (p q : Fin 2 → ℝ) : ℝ :=
  ∑ i, p i * q i

/-- Euclidean magnitude of a two-dimensional momentum readout. -/
noncomputable def magnitude2 (p : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, (p i) ^ 2)

/--
The physical parameters appearing in the problem.  The energy fields are the
ground-state energies of `O₃` and `O₂`; the atom's ground-state energy is the
chosen zero of energy, as in the problem statement.
-/
structure PhotodissociationParameters where
  reducedPlanckConstant : ActionQuantity
  lightSpeed : DimSpeed
  oxygenAtomMass : MassQuantity
  ozoneGroundEnergy : DimEnergy
  oxygenMoleculeGroundEnergy : DimEnergy

/-- The SI readout of `ℏ`. -/
noncomputable def reducedPlanckConstantSI
    (p : PhotodissociationParameters) : ℝ :=
  scalarSI p.reducedPlanckConstant

/-- The SI readout of the speed of light. -/
noncomputable def lightSpeedSI (p : PhotodissociationParameters) : ℝ :=
  speedSI p.lightSpeed

/-- The SI readout of the mass `m` of one oxygen atom. -/
noncomputable def oxygenAtomMassSI (p : PhotodissociationParameters) : ℝ :=
  scalarSI p.oxygenAtomMass

/-- The energy gap `ΔU = U_f - U_i`, in joules. -/
noncomputable def energyDifferenceSI
    (p : PhotodissociationParameters) : ℝ :=
  scalarSI p.oxygenMoleculeGroundEnergy -
    scalarSI p.ozoneGroundEnergy

/--
Physical parameter and angle conditions.  The upper bound on `ΔU` is the
uniform discriminant condition for nonrelativistic two-fragment kinematics and
also keeps the square-root arguments in the recorded answer nonnegative
throughout `0 ≤ θ ≤ π`.
-/
structure ValidPhotodissociationParameters
    (p : PhotodissociationParameters) (θ : ℝ) : Prop where
  reducedPlanckConstant_pos : 0 < reducedPlanckConstantSI p
  lightSpeed_pos : 0 < lightSpeedSI p
  oxygenAtomMass_pos : 0 < oxygenAtomMassSI p
  energyDifference_nonneg : 0 ≤ energyDifferenceSI p
  twice_energyDifference_le_restEnergy :
    2 * energyDifferenceSI p ≤ oxygenAtomMassSI p * (lightSpeedSI p) ^ 2
  angle_nonneg : 0 ≤ θ
  angle_le_pi : θ ≤ Real.pi

/--
`DissociationAt p θ ω` states the governing laws for a photon of angular
frequency `ω`, measured in radians per second, producing the two fragments at
the Figure 1c angle `θ`.

The final `O₂` mass is `2m`, hence its kinetic energy denominator is
`2 * (2m)`.  The atomic oxygen denominator is `2m`.
-/
def DissociationAt
    (p : PhotodissociationParameters) (θ ω : ℝ) : Prop :=
  0 ≤ ω ∧
    ∃ photonMomentum oxygenMoleculeMomentum oxygenAtomMomentum :
        MomentumQuantity2,
      momentumSI photonMomentum =
          momentumSI oxygenMoleculeMomentum + momentumSI oxygenAtomMomentum ∧
      magnitude2 (momentumSI photonMomentum) =
          reducedPlanckConstantSI p * ω / lightSpeedSI p ∧
      dot2 (momentumSI photonMomentum) (momentumSI oxygenMoleculeMomentum) =
          magnitude2 (momentumSI photonMomentum) *
            magnitude2 (momentumSI oxygenMoleculeMomentum) * Real.cos θ ∧
      reducedPlanckConstantSI p * ω =
          energyDifferenceSI p +
            magnitude2 (momentumSI oxygenMoleculeMomentum) ^ 2 /
              (2 * (2 * oxygenAtomMassSI p)) +
            magnitude2 (momentumSI oxygenAtomMomentum) ^ 2 /
              (2 * oxygenAtomMassSI p)

/--
The proposed angular frequency is feasible and no smaller feasible
nonnegative frequency exists at the same outgoing `O₂` angle.
-/
def IsMinimumDissociationFrequency
    (p : PhotodissociationParameters) (θ : ℝ)
    (ωmin : AngularFrequencyQuantity) : Prop :=
  DissociationAt p θ (scalarSI ωmin) ∧
    ∀ ω : ℝ, DissociationAt p θ ω → scalarSI ωmin ≤ ω

/--
The recorded answer for the minimum photon angular frequency.  For acute and
right angles it is the angle-dependent expression; for obtuse angles it
saturates at the value obtained at `θ = π / 2`.
-/
theorem minimumAngularFrequency_eq
    (p : PhotodissociationParameters) (θ : ℝ)
    (ωmin : AngularFrequencyQuantity)
    (hvalid : ValidPhotodissociationParameters p θ)
    (hminimum : IsMinimumDissociationFrequency p θ ωmin) :
    (θ ≤ Real.pi / 2 →
      scalarSI ωmin =
        (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
            (1 - Real.sqrt
              (1 -
                2 * energyDifferenceSI p /
                    (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) *
                  (2 * (Real.sin θ) ^ 2 + 1)))) /
          (reducedPlanckConstantSI p * (2 * (Real.sin θ) ^ 2 + 1))) ∧
    (Real.pi / 2 ≤ θ →
      scalarSI ωmin =
        (oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
            (1 - Real.sqrt
              (1 -
                2 * energyDifferenceSI p /
                  (oxygenAtomMassSI p * (lightSpeedSI p) ^ 2)))) /
          reducedPlanckConstantSI p) := by
  rcases hvalid with ⟨hℏ, hc, hm, hΔU, hrest, hθnonneg, hθlepi⟩
  rcases hminimum with ⟨hminFeasible, hleast⟩
  let momentumOfSI (v : Fin 2 → ℝ) : MomentumQuantity2 :=
    CarriesDimension.toDimensionful UnitChoices.SI ⟨v⟩
  have momentumSI_momentumOfSI (v : Fin 2 → ℝ) :
      momentumSI (momentumOfSI v) = v := by
    funext i
    simp [momentumOfSI, momentumSI,
      CarriesDimension.toDimensionful_apply_apply]
  have magnitude2_sq (v : Fin 2 → ℝ) :
      magnitude2 v ^ 2 = ∑ i, (v i) ^ 2 := by
    rw [magnitude2, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have momentum_difference_sq
      (photon molecule atom : Fin 2 → ℝ)
      (hconservation : photon = molecule + atom) :
      magnitude2 atom ^ 2 =
        magnitude2 photon ^ 2 + magnitude2 molecule ^ 2 -
          2 * dot2 photon molecule := by
    have hatom : atom = photon - molecule := by
      funext i
      have hi := congrFun hconservation i
      dsimp at hi ⊢
      linarith
    rw [magnitude2_sq atom, magnitude2_sq photon,
      magnitude2_sq molecule, hatom]
    simp only [Fin.sum_univ_two, dot2, Pi.sub_apply]
    ring
  constructor
  · intro hθacute
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by nlinarith [Real.pi_pos]) hθacute
    let A : ℝ := 2 * (Real.sin θ) ^ 2 + 1
    have hApos : 0 < A := by
      dsimp [A]
      nlinarith [sq_nonneg (Real.sin θ)]
    have hAle : A ≤ 3 := by
      dsimp [A]
      nlinarith [Real.sin_sq_le_one θ]
    have hAΔU : 2 * energyDifferenceSI p * A ≤
        3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 := by
      nlinarith [mul_nonneg hΔU (sub_nonneg.mpr hAle)]
    let D : ℝ :=
      1 -
        2 * energyDifferenceSI p /
            (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) * A
    have hDnonneg : 0 ≤ D := by
      dsimp [D]
      rw [show
        2 * energyDifferenceSI p /
              (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) * A =
            (2 * energyDifferenceSI p * A) /
              (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) by
          ring]
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hAΔU
    have hDle : D ≤ 1 := by
      dsimp [D]
      have hterm :
          0 ≤
            2 * energyDifferenceSI p /
                (3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) * A := by
        positivity
      linarith
    let S : ℝ := Real.sqrt D
    have hSnonneg : 0 ≤ S := Real.sqrt_nonneg D
    have hSsq : S ^ 2 = D := by
      dsimp [S]
      exact Real.sq_sqrt hDnonneg
    have hSle : S ≤ 1 := by
      nlinarith only [hSsq, hDle, hSnonneg]
    let W : ℝ :=
      3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 * (1 - S) /
        (reducedPlanckConstantSI p * A)
    have hWnonneg : 0 ≤ W := by
      dsimp [W]
      positivity
    have hWenergy :
        reducedPlanckConstantSI p * W =
          energyDifferenceSI p +
            A * (reducedPlanckConstantSI p * W) ^ 2 /
              (6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) := by
      dsimp [W]
      dsimp [D] at hSsq
      field_simp [ne_of_gt hℏ, ne_of_gt hc, ne_of_gt hm,
        ne_of_gt hApos] at hSsq ⊢
      nlinarith only [hSsq]
    have hWrest :
        A * (reducedPlanckConstantSI p * W) ≤
          3 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 := by
      dsimp [W]
      field_simp [ne_of_gt hℏ, ne_of_gt hApos]
      nlinarith only [hSnonneg, mul_pos hm (sq_pos_of_pos hc)]
    let qcand : ℝ :=
      reducedPlanckConstantSI p * W / lightSpeedSI p
    have hqcand : 0 ≤ qcand := by
      dsimp [qcand]
      positivity
    let rcand : ℝ := 2 * qcand * Real.cos θ / 3
    have hrcand : 0 ≤ rcand := by
      dsimp [rcand]
      positivity
    let photonVector : Fin 2 → ℝ := ![qcand, 0]
    let moleculeVector : Fin 2 → ℝ :=
      ![rcand * Real.cos θ, rcand * Real.sin θ]
    let atomVector : Fin 2 → ℝ := photonVector - moleculeVector
    have hphotonMagnitude : magnitude2 photonVector = qcand := by
      rw [magnitude2]
      simp only [photonVector, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, pow_two, mul_zero, add_zero]
      simpa [pow_two] using Real.sqrt_sq hqcand
    have hmoleculeMagnitude : magnitude2 moleculeVector = rcand := by
      rw [magnitude2]
      simp only [moleculeVector, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [show
        (rcand * Real.cos θ) ^ 2 + (rcand * Real.sin θ) ^ 2 =
            rcand ^ 2 by
          nlinarith [Real.sin_sq_add_cos_sq θ]]
      exact Real.sqrt_sq hrcand
    have hcandidateDot :
        dot2 photonVector moleculeVector =
          qcand * rcand * Real.cos θ := by
      simp only [dot2, photonVector, moleculeVector, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hatomMagnitudeSq :
        magnitude2 atomVector ^ 2 =
          qcand ^ 2 + rcand ^ 2 -
            2 * qcand * rcand * Real.cos θ := by
      rw [magnitude2_sq atomVector]
      simp only [atomVector, photonVector, moleculeVector,
        Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hcandidateKinetic :
        magnitude2 moleculeVector ^ 2 /
              (2 * (2 * oxygenAtomMassSI p)) +
            magnitude2 atomVector ^ 2 /
              (2 * oxygenAtomMassSI p) =
          A * (reducedPlanckConstantSI p * W) ^ 2 /
            (6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) := by
      rw [hmoleculeMagnitude, hatomMagnitudeSq]
      have hqmul :
          qcand * lightSpeedSI p = reducedPlanckConstantSI p * W := by
        dsimp [qcand]
        field_simp [ne_of_gt hc]
      have hqSq :
          qcand ^ 2 * (lightSpeedSI p) ^ 2 =
            (reducedPlanckConstantSI p * W) ^ 2 := by
        rw [← hqmul]
        ring
      dsimp [A, rcand]
      field_simp [ne_of_gt hm, ne_of_gt hc]
      nlinarith only [Real.sin_sq_add_cos_sq θ, hqSq]
    have hcandidate : DissociationAt p θ W := by
      refine ⟨hWnonneg, ?_⟩
      refine ⟨momentumOfSI photonVector, momentumOfSI moleculeVector,
        momentumOfSI atomVector, ?_, ?_, ?_, ?_⟩
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI,
          momentumSI_momentumOfSI]
        dsimp [atomVector]
        abel
      · rw [momentumSI_momentumOfSI, hphotonMagnitude]
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI,
          hcandidateDot, hphotonMagnitude, hmoleculeMagnitude]
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI,
          add_assoc, hcandidateKinetic]
        exact hWenergy
    have hminLe : scalarSI ωmin ≤ W := hleast W hcandidate
    have hWLe : W ≤ scalarSI ωmin := by
      rcases hminFeasible with
        ⟨hωnonneg, photonMomentum, moleculeMomentum, atomMomentum,
          hconservation, hphotonMomentum, hangle, henergy⟩
      let w : ℝ := scalarSI ωmin
      let q : ℝ := magnitude2 (momentumSI photonMomentum)
      let r : ℝ := magnitude2 (momentumSI moleculeMomentum)
      let a : ℝ := magnitude2 (momentumSI atomMomentum)
      have hqnonneg : 0 ≤ q := by
        dsimp [q, magnitude2]
        exact Real.sqrt_nonneg _
      have hrnonneg : 0 ≤ r := by
        dsimp [r, magnitude2]
        exact Real.sqrt_nonneg _
      have hatomSq :
          a ^ 2 =
            q ^ 2 + r ^ 2 - 2 * q * r * Real.cos θ := by
        have hdiff := momentum_difference_sq
          (momentumSI photonMomentum)
          (momentumSI moleculeMomentum)
          (momentumSI atomMomentum) hconservation
        rw [hangle] at hdiff
        dsimp [q, r, a]
        convert hdiff using 1
        ring
      have hqmul :
          q * lightSpeedSI p = reducedPlanckConstantSI p * w := by
        have hqeq :
            q =
              reducedPlanckConstantSI p * w / lightSpeedSI p := by
          simpa [q, w] using hphotonMomentum
        field_simp [ne_of_gt hc] at hqeq
        exact hqeq
      have henergy4 :
          4 * oxygenAtomMassSI p *
                (reducedPlanckConstantSI p * w) =
            4 * oxygenAtomMassSI p * energyDifferenceSI p +
              r ^ 2 + 2 * a ^ 2 := by
        have he :
            reducedPlanckConstantSI p * w =
              energyDifferenceSI p +
                r ^ 2 / (2 * (2 * oxygenAtomMassSI p)) +
                a ^ 2 / (2 * oxygenAtomMassSI p) := by
          simpa [w, r, a] using henergy
        field_simp [ne_of_gt hm] at he ⊢
        nlinarith only [he]
      have hcompletion :
          0 ≤ (3 * r - 2 * q * Real.cos θ) ^ 2 := sq_nonneg _
      have hkineticLower :
          2 * A * q ^ 2 ≤ 3 * (r ^ 2 + 2 * a ^ 2) := by
        dsimp [A]
        nlinarith only [hatomSq, hcompletion,
          Real.sin_sq_add_cos_sq θ]
      have hkineticLower' :
          A * q ^ 2 ≤
            6 * oxygenAtomMassSI p *
              (reducedPlanckConstantSI p * w - energyDifferenceSI p) := by
        nlinarith only [henergy4, hkineticLower]
      have hmul := mul_le_mul_of_nonneg_right hkineticLower'
        (sq_nonneg (lightSpeedSI p))
      have hqSq :
          q ^ 2 * (lightSpeedSI p) ^ 2 =
            (reducedPlanckConstantSI p * w) ^ 2 := by
        rw [← hqmul]
        ring
      have hmul' :
          A * (reducedPlanckConstantSI p * w) ^ 2 ≤
            6 * oxygenAtomMassSI p *
                (reducedPlanckConstantSI p * w - energyDifferenceSI p) *
              (lightSpeedSI p) ^ 2 := by
        rw [← hqSq]
        simpa only [mul_assoc] using hmul
      have hquadratic :
          6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
                energyDifferenceSI p +
              A * (reducedPlanckConstantSI p * w) ^ 2 ≤
            6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
              (reducedPlanckConstantSI p * w) := by
        nlinarith only [hmul']
      by_contra hn
      have hwlt : w < W := by
        exact lt_of_not_ge (by simpa [w] using hn)
      have hxlt :
          reducedPlanckConstantSI p * w <
            reducedPlanckConstantSI p * W := by
        nlinarith only [hwlt, hℏ]
      have hsum :
          A * (reducedPlanckConstantSI p * w +
                reducedPlanckConstantSI p * W) <
            6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 := by
        have hAmul := mul_lt_mul_of_pos_left hxlt hApos
        nlinarith only [hAmul, hWrest]
      have hWenergyClear :
          6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
                energyDifferenceSI p +
              A * (reducedPlanckConstantSI p * W) ^ 2 =
            6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
              (reducedPlanckConstantSI p * W) := by
        field_simp [ne_of_gt hm, ne_of_gt hc] at hWenergy
        nlinarith only [hWenergy]
      have hproduct :
          0 <
            (reducedPlanckConstantSI p * W -
                reducedPlanckConstantSI p * w) *
              (6 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 -
                A * (reducedPlanckConstantSI p * w +
                  reducedPlanckConstantSI p * W)) :=
        mul_pos (sub_pos.mpr hxlt) (sub_pos.mpr hsum)
      nlinarith only [hquadratic, hWenergyClear, hproduct]
    have heq : scalarSI ωmin = W := le_antisymm hminLe hWLe
    simpa only [W, S, D, A] using heq
  · intro hθobtuse
    have hcos : Real.cos θ ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hθobtuse
        (by nlinarith [Real.pi_pos])
    let D : ℝ :=
      1 -
        2 * energyDifferenceSI p /
          (oxygenAtomMassSI p * (lightSpeedSI p) ^ 2)
    have hDnonneg : 0 ≤ D := by
      dsimp [D]
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hrest
    have hDle : D ≤ 1 := by
      dsimp [D]
      have hterm :
          0 ≤
            2 * energyDifferenceSI p /
              (oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) := by
        positivity
      linarith
    let S : ℝ := Real.sqrt D
    have hSnonneg : 0 ≤ S := Real.sqrt_nonneg D
    have hSsq : S ^ 2 = D := by
      dsimp [S]
      exact Real.sq_sqrt hDnonneg
    have hSle : S ≤ 1 := by
      nlinarith only [hSsq, hDle, hSnonneg]
    let W : ℝ :=
      oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 * (1 - S) /
        reducedPlanckConstantSI p
    have hWnonneg : 0 ≤ W := by
      dsimp [W]
      positivity
    have hWenergy :
        reducedPlanckConstantSI p * W =
          energyDifferenceSI p +
            (reducedPlanckConstantSI p * W) ^ 2 /
              (2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) := by
      dsimp [W]
      dsimp [D] at hSsq
      field_simp [ne_of_gt hℏ, ne_of_gt hc, ne_of_gt hm] at hSsq ⊢
      nlinarith only [hSsq]
    have hWrest :
        reducedPlanckConstantSI p * W ≤
          oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 := by
      dsimp [W]
      field_simp [ne_of_gt hℏ]
      nlinarith only [hSnonneg, mul_pos hm (sq_pos_of_pos hc)]
    let qcand : ℝ :=
      reducedPlanckConstantSI p * W / lightSpeedSI p
    have hqcand : 0 ≤ qcand := by
      dsimp [qcand]
      positivity
    let photonVector : Fin 2 → ℝ := ![qcand, 0]
    let zeroVector : Fin 2 → ℝ := 0
    have hphotonMagnitude : magnitude2 photonVector = qcand := by
      rw [magnitude2]
      simp only [photonVector, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, pow_two, mul_zero, add_zero]
      simpa [pow_two] using Real.sqrt_sq hqcand
    have hzeroMagnitude : magnitude2 zeroVector = 0 := by
      simp [magnitude2, zeroVector]
    have hcandidateKinetic :
        magnitude2 zeroVector ^ 2 /
              (2 * (2 * oxygenAtomMassSI p)) +
            magnitude2 photonVector ^ 2 /
              (2 * oxygenAtomMassSI p) =
          (reducedPlanckConstantSI p * W) ^ 2 /
            (2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2) := by
      rw [hzeroMagnitude, hphotonMagnitude]
      have hqmul :
          qcand * lightSpeedSI p = reducedPlanckConstantSI p * W := by
        dsimp [qcand]
        field_simp [ne_of_gt hc]
      have hqSq :
          qcand ^ 2 * (lightSpeedSI p) ^ 2 =
            (reducedPlanckConstantSI p * W) ^ 2 := by
        rw [← hqmul]
        ring
      field_simp [ne_of_gt hm, ne_of_gt hc]
      nlinarith only [hqSq]
    have hcandidate : DissociationAt p θ W := by
      refine ⟨hWnonneg, ?_⟩
      refine ⟨momentumOfSI photonVector, momentumOfSI zeroVector,
        momentumOfSI photonVector, ?_, ?_, ?_, ?_⟩
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI]
        simp [zeroVector]
      · rw [momentumSI_momentumOfSI, hphotonMagnitude]
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI,
          hzeroMagnitude]
        simp [dot2, zeroVector]
      · rw [momentumSI_momentumOfSI, momentumSI_momentumOfSI,
          add_assoc, hcandidateKinetic]
        exact hWenergy
    have hminLe : scalarSI ωmin ≤ W := hleast W hcandidate
    have hWLe : W ≤ scalarSI ωmin := by
      rcases hminFeasible with
        ⟨hωnonneg, photonMomentum, moleculeMomentum, atomMomentum,
          hconservation, hphotonMomentum, hangle, henergy⟩
      let w : ℝ := scalarSI ωmin
      let q : ℝ := magnitude2 (momentumSI photonMomentum)
      let r : ℝ := magnitude2 (momentumSI moleculeMomentum)
      let a : ℝ := magnitude2 (momentumSI atomMomentum)
      have hqnonneg : 0 ≤ q := by
        dsimp [q, magnitude2]
        exact Real.sqrt_nonneg _
      have hrnonneg : 0 ≤ r := by
        dsimp [r, magnitude2]
        exact Real.sqrt_nonneg _
      have hatomSq :
          a ^ 2 =
            q ^ 2 + r ^ 2 - 2 * q * r * Real.cos θ := by
        have hdiff := momentum_difference_sq
          (momentumSI photonMomentum)
          (momentumSI moleculeMomentum)
          (momentumSI atomMomentum) hconservation
        rw [hangle] at hdiff
        dsimp [q, r, a]
        convert hdiff using 1
        ring
      have hqmul :
          q * lightSpeedSI p = reducedPlanckConstantSI p * w := by
        have hqeq :
            q =
              reducedPlanckConstantSI p * w / lightSpeedSI p := by
          simpa [q, w] using hphotonMomentum
        field_simp [ne_of_gt hc] at hqeq
        exact hqeq
      have henergy4 :
          4 * oxygenAtomMassSI p *
                (reducedPlanckConstantSI p * w) =
            4 * oxygenAtomMassSI p * energyDifferenceSI p +
              r ^ 2 + 2 * a ^ 2 := by
        have he :
            reducedPlanckConstantSI p * w =
              energyDifferenceSI p +
                r ^ 2 / (2 * (2 * oxygenAtomMassSI p)) +
                a ^ 2 / (2 * oxygenAtomMassSI p) := by
          simpa [w, r, a] using henergy
        field_simp [ne_of_gt hm] at he ⊢
        nlinarith only [he]
      have hqrcos : q * r * Real.cos θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hqnonneg hrnonneg) hcos
      have hkineticLower : q ^ 2 ≤ a ^ 2 := by
        nlinarith only [hatomSq, hqrcos, sq_nonneg r]
      have hkineticLower' :
          q ^ 2 ≤
            2 * oxygenAtomMassSI p *
              (reducedPlanckConstantSI p * w - energyDifferenceSI p) := by
        nlinarith only [henergy4, hkineticLower, sq_nonneg r]
      have hmul := mul_le_mul_of_nonneg_right hkineticLower'
        (sq_nonneg (lightSpeedSI p))
      have hqSq :
          q ^ 2 * (lightSpeedSI p) ^ 2 =
            (reducedPlanckConstantSI p * w) ^ 2 := by
        rw [← hqmul]
        ring
      have hmul' :
          (reducedPlanckConstantSI p * w) ^ 2 ≤
            2 * oxygenAtomMassSI p *
                (reducedPlanckConstantSI p * w - energyDifferenceSI p) *
              (lightSpeedSI p) ^ 2 := by
        rw [← hqSq]
        simpa only [mul_assoc] using hmul
      have hquadratic :
          2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
                energyDifferenceSI p +
              (reducedPlanckConstantSI p * w) ^ 2 ≤
            2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
              (reducedPlanckConstantSI p * w) := by
        nlinarith only [hmul']
      by_contra hn
      have hwlt : w < W := by
        exact lt_of_not_ge (by simpa [w] using hn)
      have hxlt :
          reducedPlanckConstantSI p * w <
            reducedPlanckConstantSI p * W := by
        nlinarith only [hwlt, hℏ]
      have hsum :
          reducedPlanckConstantSI p * w +
              reducedPlanckConstantSI p * W <
            2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 := by
        nlinarith only [hxlt, hWrest]
      have hWenergyClear :
          2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
                energyDifferenceSI p +
              (reducedPlanckConstantSI p * W) ^ 2 =
            2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 *
              (reducedPlanckConstantSI p * W) := by
        field_simp [ne_of_gt hm, ne_of_gt hc] at hWenergy
        nlinarith only [hWenergy]
      have hproduct :
          0 <
            (reducedPlanckConstantSI p * W -
                reducedPlanckConstantSI p * w) *
              (2 * oxygenAtomMassSI p * (lightSpeedSI p) ^ 2 -
                (reducedPlanckConstantSI p * w +
                  reducedPlanckConstantSI p * W)) :=
        mul_pos (sub_pos.mpr hxlt) (sub_pos.mpr hsum)
      nlinarith only [hquadratic, hWenergyClear, hproduct]
    have heq : scalarSI ωmin = W := le_antisymm hminLe hWLe
    simpa only [W, S, D] using heq

end IPhO2026Problems.IPhO2026_1_C_1
