import ArchonPhysics.ResonantThreeWaveKineticLInfinityIntegratingFactor

/-!
# Forward invariance of the nonnegative cone for the unclipped L-infinity flow

The quasipositive collision field is conjugated by an integrating factor to
a field that is genuinely nonnegative on a local norm ball.  The closed-cone
Picard theorem then constructs a nonnegative fixed point.  Undoing the
conjugation gives a solution of the original, genuinely unclipped RN
collision ODE and the usual local Lipschitz theorem gives uniqueness.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityNonnegativeLocalFlow

open Filter Function MeasureTheory Metric Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticLInfinityIntegratingFactor
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositivePicard
open scoped ENNReal NNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Forward-time version of the genuine unclipped RN collision equation. -/
def SolvesForwardRNCollisionODEOn
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision) (epsilon : Real)
    (curve : Real → CanonicalLInfinity collision) : Prop :=
  curve 0 = initial ∧
    ∀ t ∈ Icc 0 epsilon,
      HasDerivWithinAt curve (rnCollisionVectorField collision g (curve t))
        (Icc 0 epsilon) t

/-- The local uniqueness class used below: trajectories stay in the closed
origin ball selected by the Picard construction. -/
def RemainsInCanonicalLInfinityOriginBall
    (collision : ResonantThreeWaveMeasure Mode) (radius epsilon : Real)
    (curve : Real → CanonicalLInfinity collision) : Prop :=
  ∀ t ∈ Icc 0 epsilon,
    curve t ∈ closedBall (0 : CanonicalLInfinity collision) radius

/-- Nonnegative canonical `L-infinity` data generate a unique nonnegative
forward local solution of the original unclipped collision equation.

The returned radius is exactly `‖initial‖ + a`.  Uniqueness is asserted among
all forward solutions remaining in that origin ball, so this theorem connects
directly to the existing unclipped local Lipschitz interface.
-/
theorem exists_unique_forward_local_rnCollisionODE_nonnegative
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    (initial : CanonicalLInfinity collision) (hinitial : 0 ≤ initial)
    (a : NNReal) (ha : 0 < a) :
    let radius : Real := ‖initial‖ + (a : Real)
    ∃ epsilon : Real, 0 < epsilon ∧
      ∃ curve : Real → CanonicalLInfinity collision,
        SolvesForwardRNCollisionODEOn collision g initial epsilon curve ∧
        RemainsInCanonicalLInfinityOriginBall collision radius epsilon curve ∧
        (∀ t ∈ Icc 0 epsilon, 0 ≤ curve t) ∧
        ∀ other : Real → CanonicalLInfinity collision,
          SolvesForwardRNCollisionODEOn collision g initial epsilon other →
          RemainsInCanonicalLInfinityOriginBall collision radius epsilon other →
          EqOn curve other (Icc 0 epsilon) := by
  dsimp only
  let radius : Real := ‖initial‖ + (a : Real)
  let rate : Real := dampingRate g radius
  let fieldBound : Real :=
    Real.exp rate * (3 * g ^ 2 * radius ^ 2) + rate * radius
  let L : NNReal := Real.toNNReal fieldBound
  let K : NNReal := Real.toNNReal
    (Real.exp rate * (6 * g ^ 2 * radius) + rate)
  let epsilon : Real := min 1 ((a : Real) / ((L : Real) + 1))
  have hradius : 0 ≤ radius := by
    dsimp only [radius]
    positivity
  have hrate : 0 ≤ rate := dampingRate_nonnegative g radius hradius
  have hfieldBound : 0 ≤ fieldBound := by
    dsimp only [fieldBound]
    positivity
  have hL : (L : Real) = fieldBound := by
    exact Real.coe_toNNReal fieldBound hfieldBound
  have haReal : 0 < (a : Real) := NNReal.coe_pos.2 ha
  have hquotient : 0 < (a : Real) / ((L : Real) + 1) := by positivity
  have hepsilon : 0 < epsilon := by
    exact lt_min zero_lt_one hquotient
  have hepsilonOne : epsilon ≤ 1 := min_le_left _ _
  have hepsilonQuotient :
      epsilon ≤ (a : Real) / ((L : Real) + 1) := min_le_right _ _
  let t₀ : Icc (0 : Real) epsilon :=
    ⟨0, left_mem_Icc.mpr hepsilon.le⟩
  have hpl : IsPicardLindelof
      (integratingFactorField collision g radius) t₀ initial a 0 L K := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      exact (lipschitzOnWith_integratingFactorField collision g radius t
        hradius ht.1 (ht.2.trans hepsilonOne)).mono
          (closedBall_subset_closedBall_zero collision initial a)
    · intro action _haction
      exact (continuous_integratingFactorField_time collision g radius action).continuousOn
    · intro t ht action haction
      have hnorm : ‖action‖ ≤ radius := by
        have := closedBall_subset_closedBall_zero collision initial a haction
        simpa only [mem_closedBall_iff_norm, sub_zero] using this
      rw [hL]
      exact norm_integratingFactorField_le collision g radius t hradius
        ht.1 (ht.2.trans hepsilonOne) action hnorm
    · simp only [t₀, sub_zero, max_eq_left hepsilon.le,
        NNReal.coe_zero]
      calc
        (L : Real) * epsilon ≤
            (L : Real) * ((a : Real) / ((L : Real) + 1)) := by
          gcongr
        _ = ((L : Real) / ((L : Real) + 1)) * (a : Real) := by ring
        _ ≤ 1 * (a : Real) := by
          gcongr
          exact (div_le_one (by positivity : 0 < (L : Real) + 1)).2
            (by linarith)
        _ = (a : Real) := one_mul _
  have hinitialBall : initial ∈ closedBall initial (((0 : NNReal) : Real)) :=
    mem_closedBall_self le_rfl
  have hfieldPositive :
      ∀ t ∈ Icc (0 : Real) epsilon,
        ∀ action ∈ closedBall initial (a : Real),
          0 ≤ action →
            0 ≤ integratingFactorField collision g radius t action := by
    intro t ht action haction hactionPositive
    have hnorm : ‖action‖ ≤ radius := by
      have := closedBall_subset_closedBall_zero collision initial a haction
      simpa only [mem_closedBall_iff_norm, sub_zero] using this
    exact integratingFactorField_nonnegative collision g radius t hradius ht.1
      action hnorm hactionPositive
  obtain ⟨alpha, halphaFixed, halphaPositive⟩ :=
    exists_isFixedPt_next_isNonnegative hpl hinitialBall rfl hinitial
      hfieldPositive
  let transformed : Real → CanonicalLInfinity collision := alpha.compProj
  have htransformedZero : transformed 0 = initial := by
    change alpha.compProj (t₀ : Real) = initial
    rw [ODE.FunSpace.compProj_val, ← halphaFixed,
      ODE.FunSpace.next_apply₀]
  have htransformedDeriv : ∀ t ∈ Icc (0 : Real) epsilon,
      HasDerivWithinAt transformed
        (integratingFactorField collision g radius t (transformed t))
        (Icc 0 epsilon) t := by
    intro t ht
    dsimp only [transformed]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2
      hpl.continuousOn_uncurry alpha.continuous_compProj.continuousOn
      (fun _ _ ↦ alpha.compProj_mem_closedBall hpl.mul_max_le)
      initial ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← halphaFixed]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have htransformedPositive : ∀ t ∈ Icc (0 : Real) epsilon,
      0 ≤ transformed t := by
    intro t ht
    change 0 ≤ alpha.compProj t
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact halphaPositive ⟨t, ht⟩
  have htransformedNorm : ∀ t ∈ Icc (0 : Real) epsilon,
      ‖transformed t‖ ≤ radius := by
    intro t ht
    have hball := alpha.compProj_mem_closedBall hpl.mul_max_le
      (t := t)
    have hnorm := closedBall_subset_closedBall_zero collision initial a hball
    simpa only [transformed, mem_closedBall_iff_norm, sub_zero] using hnorm
  let curve : Real → CanonicalLInfinity collision :=
    (fun t ↦ Real.exp ((-rate) * t)) • transformed
  have hcurveZero : curve 0 = initial := by
    change Real.exp ((-rate) * 0) • transformed 0 = initial
    simp only [mul_zero, Real.exp_zero, one_smul, htransformedZero]
  have hcurvePositive : ∀ t ∈ Icc (0 : Real) epsilon, 0 ≤ curve t := by
    intro t ht
    change 0 ≤ Real.exp ((-rate) * t) • transformed t
    exact smul_nonnegative collision (Real.exp_pos _).le
      (htransformedPositive t ht)
  have hcurveNorm : ∀ t ∈ Icc (0 : Real) epsilon, ‖curve t‖ ≤ radius := by
    intro t ht
    change ‖Real.exp ((-rate) * t) • transformed t‖ ≤ radius
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexponent : (-rate) * t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) ht.1
    have hexp : Real.exp ((-rate) * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr hexponent
    calc
      Real.exp ((-rate) * t) * ‖transformed t‖ ≤
          1 * ‖transformed t‖ := by gcongr
      _ = ‖transformed t‖ := one_mul _
      _ ≤ radius := htransformedNorm t ht
  have hcurveDeriv : ∀ t ∈ Icc (0 : Real) epsilon,
      HasDerivWithinAt curve (rnCollisionVectorField collision g (curve t))
        (Icc 0 epsilon) t := by
    intro t ht
    have hscalarAt : HasDerivAt
        (fun u : Real ↦ Real.exp ((-rate) * u))
        ((-rate) * Real.exp ((-rate) * t)) t := by
      have hinner : HasDerivAt (fun u : Real ↦ (-rate) * u) (-rate) t :=
        hasDerivAt_const_mul (-rate)
      simpa only [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp _).comp t hinner
    have hproduct := hscalarAt.hasDerivWithinAt.smul
      (htransformedDeriv t ht)
    have hproductCurve : HasDerivWithinAt curve
        (Real.exp ((-rate) * t) •
            integratingFactorField collision g radius t (transformed t) +
          ((-rate) * Real.exp ((-rate) * t)) • transformed t)
        (Icc 0 epsilon) t := by
      exact hproduct
    apply hproductCurve.congr_deriv
    simp only [integratingFactorField, dampedState, rnCollisionVectorField]
    have hcancel : Real.exp ((-rate) * t) * Real.exp (rate * t) = 1 := by
      rw [← Real.exp_add]
      simp
    simp only [rate, curve, neg_mul] at hcancel ⊢
    rw [smul_add, smul_smul, smul_smul, hcancel, one_mul]
    module
  have hcurveBall : RemainsInCanonicalLInfinityOriginBall collision radius
      epsilon curve := by
    intro t ht
    simpa only [mem_closedBall_iff_norm, sub_zero] using hcurveNorm t ht
  have hsolution : SolvesForwardRNCollisionODEOn collision g initial epsilon curve :=
    ⟨hcurveZero, hcurveDeriv⟩
  refine ⟨epsilon, hepsilon, curve, hsolution, hcurveBall,
    hcurvePositive, ?_⟩
  intro other hother hotherBall
  let Koriginal : NNReal := ‖g ^ 2‖₊ * Real.toNNReal (6 * radius)
  have horiginalLipschitz : LipschitzOnWith Koriginal
      (rnCollisionVectorField collision g)
      (closedBall (0 : CanonicalLInfinity collision) radius) := by
    simpa only [Koriginal, norm_zero, zero_add,
      Real.coe_toNNReal radius hradius] using
      lipschitzOnWith_rnCollisionVectorField_closedBall collision g
        (0 : CanonicalLInfinity collision) (Real.toNNReal radius)
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : Real ↦ rnCollisionVectorField collision g)
    (s := fun _ : Real ↦ closedBall (0 : CanonicalLInfinity collision) radius)
    (K := Koriginal)
  · intro _t _ht
    exact horiginalLipschitz
  · exact HasDerivWithinAt.continuousOn hcurveDeriv
  · intro t ht
    exact (hcurveDeriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hcurveBall t (Ico_subset_Icc_self ht)
  · exact HasDerivWithinAt.continuousOn hother.2
  · intro t ht
    exact (hother.2 t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hotherBall t (Ico_subset_Icc_self ht)
  · exact hcurveZero.trans hother.1.symm

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityNonnegativeLocalFlow
