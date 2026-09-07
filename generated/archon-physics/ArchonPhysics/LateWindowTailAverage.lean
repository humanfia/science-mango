import ArchonPhysics.LateWindowL1Stability

/-!
# Tail-window averages preserve convergence to zero

For a fixed positive left-window fraction `0 < mu < 1`, every nonnegative
continuous function converging to zero has a late-window average converging to
zero.  A finite-dimensional corollary transports pointwise `l1` convergence
of probability profiles through the same late-window averaging convention
used by the thermalization observable.
-/

namespace ArchonPhysics.LateWindowTailAverage

open Filter Set MeasureTheory
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.LateWindowL1Stability

noncomputable section

/-- Scalar late-window average on `[mu*T,T]`. -/
def scalarLateWindowAverage (f : Real -> Real) (mu T : Real) : Real :=
  ((1 - mu) * T)⁻¹ * ∫ t in mu * T..T, f t

/-- A nonnegative continuous tail converging to zero has vanishing
late-window average whenever the left endpoint also tends to infinity. -/
theorem tendsto_scalarLateWindowAverage_zero
    (f : Real -> Real) (mu : Real)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (hcontinuous : ContinuousOn f (Ici 0))
    (hnonnegative : forall t, 0 <= t -> 0 <= f t)
    (htendsto : Tendsto f atTop (nhds 0)) :
    Tendsto (scalarLateWindowAverage f mu) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at htendsto ⊢
  intro epsilon hepsilon
  have heta : 0 < epsilon / 2 := by linarith
  obtain ⟨A, hA⟩ := htendsto (epsilon / 2) heta
  refine ⟨max 1 (A / mu), ?_⟩
  intro T hT
  have hTOne : 1 <= T := (le_max_left 1 (A / mu)).trans hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hTDiv : A / mu <= T :=
    (le_max_right 1 (A / mu)).trans hT
  have hAT : A <= mu * T := by
    have := (div_le_iff₀ hmu).mp hTDiv
    nlinarith
  have hmuTNonnegative : 0 <= mu * T :=
    mul_nonneg hmu.le hTPos.le
  have hinterval : mu * T <= T := by
    nlinarith
  have hfInt : IntervalIntegrable f volume (mu * T) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hinterval]
    exact hcontinuous.mono fun t ht =>
      Set.mem_Ici.mpr (hmuTNonnegative.trans ht.1)
  have hconstInt : IntervalIntegrable (fun _ : Real => epsilon / 2)
      volume (mu * T) T := intervalIntegrable_const
  have hpointUpper : forall t, t ∈ Icc (mu * T) T -> f t <= epsilon / 2 := by
    intro t ht
    have htail := hA t (hAT.trans ht.1)
    have habs : |f t| < epsilon / 2 := by
      simpa only [Real.dist_eq, sub_zero] using htail
    exact (le_abs_self (f t)).trans habs.le
  have hintegralUpper :
      (∫ t in mu * T..T, f t) <= (T - mu * T) * (epsilon / 2) := by
    calc
      (∫ t in mu * T..T, f t) <=
          ∫ _t in mu * T..T, epsilon / 2 :=
        intervalIntegral.integral_mono_on hinterval hfInt hconstInt hpointUpper
      _ = (T - mu * T) * (epsilon / 2) := by
        rw [intervalIntegral.integral_const]
        ring
  have hintegralNonnegative : 0 <= ∫ t in mu * T..T, f t :=
    intervalIntegral.integral_nonneg hinterval fun t ht =>
      hnonnegative t (hmuTNonnegative.trans ht.1)
  have hwindowPos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmuOne) hTPos
  have haverageNonnegative : 0 <= scalarLateWindowAverage f mu T := by
    exact mul_nonneg (inv_nonneg.mpr hwindowPos.le) hintegralNonnegative
  have haverageUpper : scalarLateWindowAverage f mu T <= epsilon / 2 := by
    unfold scalarLateWindowAverage
    calc
      ((1 - mu) * T)⁻¹ * ∫ t in mu * T..T, f t <=
          ((1 - mu) * T)⁻¹ * ((T - mu * T) * (epsilon / 2)) :=
        mul_le_mul_of_nonneg_left hintegralUpper
          (inv_nonneg.mpr hwindowPos.le)
      _ = epsilon / 2 := by
        have hwindow : T - mu * T = (1 - mu) * T := by ring
        rw [hwindow, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hwindowPos), one_mul]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg haverageNonnegative]
  linarith

/-- The late-window average of a constant finite profile is the same profile. -/
theorem lateWindowAverage_const
    {Mode : Type} (profile : Mode -> Real) (mu T : Real)
    (hmuOne : mu < 1) (hT : 0 < T) :
    lateWindowAverage (fun _ : Real => profile) mu T = profile := by
  funext i
  unfold lateWindowAverage
  rw [intervalIntegral.integral_const]
  have hwindowPos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmuOne) hT
  have hmuNe : 1 - mu ≠ 0 := ne_of_gt (sub_pos.mpr hmuOne)
  have hTNe : T ≠ 0 := ne_of_gt hT
  field_simp [hmuNe, hTNe]
  ring

/-- Pointwise `l1` convergence of finite profiles to uniform energy passes to
the repository's positive-fraction late-window averages. -/
theorem tendsto_l1Distance_lateWindowAverage_uniform_zero
    {Mode : Type} [Fintype Mode] [Nonempty Mode]
    (profile : Real -> (Mode -> Real)) (mu : Real)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (hcontinuous : forall i, ContinuousOn (fun t => profile t i) (Ici 0))
    (htendsto : Tendsto
      (fun t => l1Distance (profile t) (uniformWeights : Mode -> Real))
      atTop (nhds 0)) :
    Tendsto
      (fun T => l1Distance (lateWindowAverage profile mu T)
        (uniformWeights : Mode -> Real))
      atTop (nhds 0) := by
  let distance : Real -> Real := fun t =>
    l1Distance (profile t) (uniformWeights : Mode -> Real)
  have hdistanceContinuous : ContinuousOn distance (Ici 0) := by
    unfold distance l1Distance
    apply continuousOn_finsetSum
    intro i _
    exact ((hcontinuous i).sub continuousOn_const).abs
  have hdistanceNonnegative : forall t, 0 <= t -> 0 <= distance t := by
    intro t _ht
    unfold distance l1Distance
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have htail : Tendsto (scalarLateWindowAverage distance mu)
      atTop (nhds 0) :=
    tendsto_scalarLateWindowAverage_zero distance mu hmu hmuOne
      hdistanceContinuous hdistanceNonnegative htendsto
  refine squeeze_zero' ?_ ?_ htail
  · filter_upwards with T
    unfold l1Distance
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    let constantProfile : Real -> (Mode -> Real) :=
      fun _ => (uniformWeights : Mode -> Real)
    have hinterval : mu * T <= T := by
      nlinarith
    have hprofileInt : forall i, IntervalIntegrable
        (fun t => profile t i) volume (mu * T) T := by
      intro i
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hinterval]
      exact (hcontinuous i).mono fun t ht =>
        Set.mem_Ici.mpr (mul_nonneg hmu.le hT.le |>.trans ht.1)
    have hconstantInt : forall i, IntervalIntegrable
        (fun t => constantProfile t i) volume (mu * T) T := by
      intro i
      exact intervalIntegrable_const
    have hbound := l1Distance_lateWindowAverage_le
      profile constantProfile mu T hmu.le hmuOne hT
        hprofileInt hconstantInt
    have herror : windowIntegratedL1Error profile constantProfile mu T =
        ∫ t in mu * T..T, distance t := by
      unfold windowIntegratedL1Error distance l1Distance constantProfile
      rw [← intervalIntegral.integral_finsetSum
        (fun i _ => (hprofileInt i).sub (hconstantInt i) |>.abs)]
    rw [lateWindowAverage_const
      (uniformWeights : Mode -> Real) mu T hmuOne hT] at hbound
    rw [herror] at hbound
    simpa only [scalarLateWindowAverage] using hbound

end

end ArchonPhysics.LateWindowTailAverage
