import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Physlib.Electromagnetism.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0997

open Filter

/-!
# Far axial field of an electric dipole

The figure places a charge `+q` at `y = d / 2` and a charge `-q` at
`y = -d / 2`.  Their midpoint `O` is the origin, the observation point `P`
has coordinate `y > d / 2`, and the dipole moment points along the positive
`y`-axis.  Scalar fields below are readouts in one fixed coherent system of
units: charge, length, dipole moment, permittivity, and electric-field units
are kept distinct by their field names and physical roles.

The conclusion uses `Asymptotics.IsEquivalent` at `Filter.atTop` to give a
precise meaning to the approximation `y ≫ d`.
-/

/-- The unit vector in the positive `y` direction of the pictured coordinate system. -/
def yAxisUnit : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- A point with coordinate `(0, y, 0)` on the figure's `y`-axis. -/
def pointOnYAxis (y : ℝ) : Space 3 :=
  ⟨fun i => if i = (1 : Fin 3) then y else 0⟩

/-- The figure's origin `O`, which is also the center of the dipole. -/
def originO : Space 3 :=
  pointOnYAxis 0

/-- The figure's observation point `P` at axial coordinate `y`. -/
def observationPointP (y : ℝ) : Space 3 :=
  pointOnYAxis y

/--
Physical quantities and fields of the centered axial dipole.

`chargeMagnitude` is the positive magnitude `q`, `separation` is the charge
spacing `d`, and `dipoleMoment` is a vector readout in charge-times-length
units.  The three electric fields retain the distinct arrows `E₊`, `E₋`, and
their total shown in the diagram.
-/
structure AxialElectricDipole where
  chargeMagnitude : ℝ
  separation : ℝ
  dipoleMoment : EuclideanSpace ℝ (Fin 3)
  positiveChargeField : Electromagnetism.ElectricField 3
  negativeChargeField : Electromagnetism.ElectricField 3
  totalElectricField : Electromagnetism.ElectricField 3

/-- The position `(0, d / 2, 0)` of the source charge `+q`. -/
def positiveChargePosition (dipole : AxialElectricDipole) : Space 3 :=
  pointOnYAxis (dipole.separation / 2)

/-- The position `(0, -d / 2, 0)` of the source charge `-q`. -/
def negativeChargePosition (dipole : AxialElectricDipole) : Space 3 :=
  pointOnYAxis (-dipole.separation / 2)

/-- The figure-labelled distance `y - d / 2` from `P` to `+q`. -/
def distancePToPositive (dipole : AxialElectricDipole) (y : ℝ) : ℝ :=
  y - dipole.separation / 2

/-- The figure-labelled distance `y + d / 2` from `P` to `-q`. -/
def distancePToNegative (dipole : AxialElectricDipole) (y : ℝ) : ℝ :=
  y + dipole.separation / 2

/-- Positivity conditions for the vacuum and the scalar figure readouts `q` and `d`. -/
def HasPhysicalParameters
    (em : Electromagnetism.EMSystem) (dipole : AxialElectricDipole) : Prop :=
  0 < em.ε₀ ∧ 0 < dipole.chargeMagnitude ∧ 0 < dipole.separation

/-- The defining dipole-moment law `p⃗ = q d ŷ`, including its `+y` direction. -/
def HasChargeSeparationDipoleMoment (dipole : AxialElectricDipole) : Prop :=
  dipole.dipoleMoment =
    (dipole.chargeMagnitude * dipole.separation) • yAxisUnit

/-!
## Assumption/target split

`HasPhysicalParameters` contains only positivity.  The moment predicate and
`SatisfiesAxialCoulombSuperposition` below contain the governing definition of
dipole moment, Coulomb's inverse-square law, the two field directions, and
superposition.  The far-field coefficient and answer choice occur only in the
conclusion of `problem_phyx_mini_0997`.
-/

/--
Coulomb's law and linear superposition on the part of the `y`-axis above both
charges.  The positive source produces an upward field, the negative source a
downward field, with the two figure distances `y - d/2` and `y + d/2`.
-/
def SatisfiesAxialCoulombSuperposition
    (em : Electromagnetism.EMSystem) (dipole : AxialElectricDipole) : Prop :=
  ∀ (t : Time) (y : ℝ), dipole.separation / 2 < y →
    dipole.positiveChargeField t (observationPointP y) =
      (em.coulombConstant * dipole.chargeMagnitude /
        (distancePToPositive dipole y) ^ 2) • yAxisUnit ∧
    dipole.negativeChargeField t (observationPointP y) =
      (-(em.coulombConstant * dipole.chargeMagnitude /
        (distancePToNegative dipole y) ^ 2)) • yAxisUnit ∧
    dipole.totalElectricField t (observationPointP y) =
      dipole.positiveChargeField t (observationPointP y) +
        dipole.negativeChargeField t (observationPointP y)

/-- The first-order truncation `1 + n x` of the binomial expansion. -/
def binomialFirstOrder (n x : ℝ) : ℝ :=
  1 + n * x

/--
The requested binomial step for inverse-square factors:
`(1 + x)⁻² = 1 - 2x + o(x)` as `x → 0`, within the stated domain `|x| < 1`.
-/
theorem inverseSquare_binomial_firstOrder :
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioo (-1) 1))
      (fun x : ℝ => ((1 + x) ^ 2)⁻¹ - binomialFirstOrder (-2) x)
      (fun x : ℝ => x) := by
  have hsum : HasDerivAt (fun x : ℝ => 1 + x) 1 0 :=
    (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).const_add 1
  have hraw := (hsum.pow 2).inv (by norm_num)
  have hfun : (fun x : ℝ => ((1 + x) ^ 2)⁻¹) =
      (((fun x : ℝ => 1 + x) ^ 2)⁻¹) := by
    ext x
    simp only [Pi.pow_apply, Pi.inv_apply]
  have hcoef : (-2 : ℝ) =
      -(2 * (1 + (0 : ℝ)) ^ (2 - 1) * 1) /
        (((fun x : ℝ => 1 + x) ^ 2) 0) ^ 2 := by
    norm_num [Pi.pow_apply]
  have hbase : HasDerivAt (fun x : ℝ => ((1 + x) ^ 2)⁻¹) (-2) 0 := by
    rw [hfun, hcoef]
    exact hraw
  have h := hbase.isLittleO
  have h' := h.mono
    (inf_le_left :
      nhdsWithin (0 : ℝ) (Set.Ioo (-1) 1) ≤ nhds 0)
  exact h'.congr'
    (Eventually.of_forall fun x => by
      dsimp [binomialFirstOrder]
      ring)
    (Eventually.of_forall fun x => by simp)

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Scalar `+y` electric-field component transcribed from each printed choice. -/
def answerAxialFieldComponent
    (choice : AnswerChoice) (p epsilon0 y : ℝ) : ℝ :=
  match choice with
  | .A => p / (4 * Real.pi * epsilon0 * y ^ 3)
  | .B => p / (2 * Real.pi * epsilon0 * y ^ 3)
  | .C => p / (2 * Real.pi * epsilon0 * y ^ 2)
  | .D => (2 * p) / (2 * Real.pi * epsilon0 * y ^ 3)

/--
For the centered dipole shown in the figure, the total electric field on the
positive axial ray is asymptotic, as `y → +∞`, to
`p / (2 π ε₀ y³)` in the positive `y` direction (answer choice B).

The scalar `dipole.dipoleMoment 1` is the `+y` component `p` of the physical
dipole-moment vector.  Neither this far-field formula nor choice B occurs in
the physical-law hypotheses.

Blueprint: `thm:physics:phyx_mini_0997:target`.
-/
theorem problem_phyx_mini_0997
    (em : Electromagnetism.EMSystem)
    (dipole : AxialElectricDipole)
    (hPhysical : HasPhysicalParameters em dipole)
    (hMoment : HasChargeSeparationDipoleMoment dipole)
    (hCoulomb : SatisfiesAxialCoulombSuperposition em dipole) :
    ∀ t : Time,
      Asymptotics.IsEquivalent atTop
        (fun y : ℝ => dipole.totalElectricField t (observationPointP y))
        (fun y : ℝ =>
          (answerAxialFieldComponent .B (dipole.dipoleMoment (1 : Fin 3))
            em.ε₀ y) • yAxisUnit) := by
  intro t
  rcases hPhysical with ⟨hepsilon, hcharge, hseparation⟩
  have hmomentComponent :
      dipole.dipoleMoment (1 : Fin 3) =
        dipole.chargeMagnitude * dipole.separation := by
    rw [hMoment]
    simp [yAxisUnit]
  let exactComponent : ℝ → ℝ := fun y =>
    em.coulombConstant * dipole.chargeMagnitude /
        (y - dipole.separation / 2) ^ 2 -
      em.coulombConstant * dipole.chargeMagnitude /
        (y + dipole.separation / 2) ^ 2
  let farComponent : ℝ → ℝ := fun y =>
    (dipole.chargeMagnitude * dipole.separation) /
      (2 * Real.pi * em.ε₀ * y ^ 3)
  have hExact :
      (fun y : ℝ => dipole.totalElectricField t (observationPointP y)) =ᶠ[atTop]
        (fun y : ℝ => exactComponent y • yAxisUnit) := by
    filter_upwards [eventually_gt_atTop (dipole.separation / 2)] with y hy
    rcases hCoulomb t y hy with ⟨hpositive, hnegative, htotal⟩
    rw [htotal, hpositive, hnegative, ← add_smul]
    congr 1
  have hScalar :
      Asymptotics.IsEquivalent atTop exactComponent farComponent := by
    have hsmall :
        Tendsto (fun y : ℝ => (dipole.separation / 2) / y)
          atTop (nhds 0) :=
      Filter.tendsto_id.const_div_atTop (dipole.separation / 2)
    have hminus :
        Tendsto (fun y : ℝ => 1 - (dipole.separation / 2) / y)
          atTop (nhds 1) := by
      convert tendsto_const_nhds.sub hsmall using 1
      all_goals norm_num
    have hplus :
        Tendsto (fun y : ℝ => 1 + (dipole.separation / 2) / y)
          atTop (nhds 1) := by
      convert tendsto_const_nhds.add hsmall using 1
      all_goals norm_num
    have hdenominator :
        Tendsto
          (fun y : ℝ =>
            (1 - (dipole.separation / 2) / y) ^ 2 *
              (1 + (dipole.separation / 2) / y) ^ 2)
          atTop (nhds 1) := by
      convert (hminus.pow 2).mul (hplus.pow 2) using 1
      all_goals norm_num
    have hratio :
        Tendsto
          (fun y : ℝ =>
            ((1 - (dipole.separation / 2) / y) ^ 2 *
              (1 + (dipole.separation / 2) / y) ^ 2)⁻¹)
          atTop (nhds 1) := by
      convert hdenominator.inv₀ (by norm_num) using 1
      all_goals norm_num
    apply Asymptotics.isEquivalent_of_tendsto_one
    refine (tendsto_congr' ?_).2 hratio
    filter_upwards [eventually_gt_atTop dipole.separation] with y hy
    have hy0 : y ≠ 0 := by nlinarith
    have hyminus : y - dipole.separation / 2 ≠ 0 := by nlinarith
    have hyplus : y + dipole.separation / 2 ≠ 0 := by nlinarith
    have htwominus : 2 * y - dipole.separation ≠ 0 := by nlinarith
    have htwoplus : 2 * y + dipole.separation ≠ 0 := by nlinarith
    have hdenminus :
        -(y * dipole.separation * 4) + y ^ 2 * 4 +
            dipole.separation ^ 2 ≠ 0 := by
      rw [show
        -(y * dipole.separation * 4) + y ^ 2 * 4 +
            dipole.separation ^ 2 =
          (2 * y - dipole.separation) ^ 2 by ring]
      exact pow_ne_zero 2 htwominus
    have hdenplus :
        y * dipole.separation * 4 + y ^ 2 * 4 +
            dipole.separation ^ 2 ≠ 0 := by
      rw [show
        y * dipole.separation * 4 + y ^ 2 * 4 +
            dipole.separation ^ 2 =
          (2 * y + dipole.separation) ^ 2 by ring]
      exact pow_ne_zero 2 htwoplus
    have hdenproduct :
        -(y ^ 2 * dipole.separation ^ 2 * 8) + y ^ 4 * 16 +
            dipole.separation ^ 4 ≠ 0 := by
      rw [show
        -(y ^ 2 * dipole.separation ^ 2 * 8) + y ^ 4 * 16 +
            dipole.separation ^ 4 =
          ((2 * y - dipole.separation) *
            (2 * y + dipole.separation)) ^ 2 by ring]
      exact pow_ne_zero 2 (mul_ne_zero htwominus htwoplus)
    dsimp [exactComponent, farComponent]
    unfold Electromagnetism.EMSystem.coulombConstant
    field_simp [hy0, hyminus, hyplus, hcharge.ne', hseparation.ne',
      hepsilon.ne', Real.pi_ne_zero]
    field_simp [hdenminus, hdenplus, hdenproduct]
    have hrightminus : y * 2 - dipole.separation ≠ 0 := by nlinarith
    have hrightplus : y * 2 + dipole.separation ≠ 0 := by nlinarith
    field_simp [hrightminus, hrightplus]
    ring
  have hVector :=
    hScalar.smul
      (Asymptotics.IsEquivalent.refl :
        Asymptotics.IsEquivalent atTop
          (fun _y : ℝ => yAxisUnit) (fun _y : ℝ => yAxisUnit))
  have hFar :
      (fun y : ℝ => farComponent y • yAxisUnit) =ᶠ[atTop]
        (fun y : ℝ =>
          (answerAxialFieldComponent .B (dipole.dipoleMoment (1 : Fin 3))
            em.ε₀ y) • yAxisUnit) := by
    filter_upwards with y
    rw [hmomentComponent]
    rfl
  exact (hVector.congr_left hExact.symm).congr_right hFar

end PhyXMiniProblems.ProblemPhyXMini0997
