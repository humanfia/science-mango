import ArchonPhysics.FiniteThreeWaveKineticGlobalFlow

namespace ArchonPhysics.FiniteNonnegativeOrthantInvariance

open Filter Metric Set Asymptotics
open scoped NNReal Topology

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise projection onto the nonnegative orthant. -/
def nonnegativeProjection (x : ι → Real) : ι → Real :=
  fun i ↦ max (x i) 0

/-- Squared distance of one coordinate to the nonnegative half-line. -/
def negativePartSquare (x : Real) : Real :=
  if x < 0 then x ^ 2 else 0

/-- Sum of squared negative parts. -/
def negativePartEnergy (x : ι → Real) : Real :=
  ∑ i, negativePartSquare (x i)

theorem negativePartSquare_nonneg (x : Real) :
    0 ≤ negativePartSquare x := by
  unfold negativePartSquare
  split_ifs <;> positivity

theorem negativePartSquare_eq_zero_iff (x : Real) :
    negativePartSquare x = 0 ↔ 0 ≤ x := by
  unfold negativePartSquare
  by_cases hx : x < 0
  · simp [hx, ne_of_lt hx]
  · simp [hx, le_of_not_gt hx]

theorem hasDerivAt_negativePartSquare (x : Real) :
    HasDerivAt negativePartSquare (if x < 0 then 2 * x else 0) x := by
  by_cases hx : x < 0
  · have heq : negativePartSquare =ᶠ[𝓝 x] fun y : Real ↦ y ^ 2 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < 0 at hy
      simp [negativePartSquare, hy]
    simpa [hx] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq heq
  · by_cases hx0 : x = 0
    · subst x
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      have hbig : negativePartSquare =O[𝓝 (0 : Real)] fun y : Real ↦ y ^ 2 :=
        IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y ↦ by
          by_cases hy : y < 0
          · simp [negativePartSquare, hy]
          · simpa [negativePartSquare, hy] using sq_nonneg y)
      have hzero : negativePartSquare 0 = 0 := by simp [negativePartSquare]
      simp only [zero_add, hzero, sub_zero, lt_self_iff_false, if_false, smul_zero]
      exact hbig.trans_isLittleO
        (isLittleO_pow_id (by norm_num : 1 < 2))
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
      have heq : negativePartSquare =ᶠ[𝓝 x] fun _y : Real ↦ 0 := by
        filter_upwards [Ioi_mem_nhds hxpos] with y hy
        change 0 < y at hy
        simp [negativePartSquare, not_lt.mpr hy.le]
      simpa [hx, hx0] using (hasDerivAt_const x 0).congr_of_eventuallyEq heq

omit [Fintype ι] in
theorem nonnegativeProjection_nonneg (x : ι → Real) (i : ι) :
    0 ≤ nonnegativeProjection x i := by
  exact le_max_right _ _

omit [Fintype ι] in
theorem nonnegativeProjection_eq_zero_of_neg {x : ι → Real} {i : ι}
    (hi : x i < 0) : nonnegativeProjection x i = 0 := by
  simp [nonnegativeProjection, hi.le]

theorem norm_nonnegativeProjection_le (x : ι → Real) :
    ‖nonnegativeProjection x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  have hi : ‖x i‖ ≤ ‖x‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl i
  by_cases hxi : x i < 0
  · simp [nonnegativeProjection, hxi.le]
  · simp only [nonnegativeProjection, max_eq_left (le_of_not_gt hxi)]
    simpa only [Real.norm_eq_abs] using hi

theorem negativePartEnergy_nonneg (x : ι → Real) :
    0 ≤ negativePartEnergy x := by
  exact Finset.sum_nonneg fun i _ ↦ negativePartSquare_nonneg (x i)

theorem negativePartSquare_le_energy (x : ι → Real) (i : ι) :
    negativePartSquare (x i) ≤ negativePartEnergy x := by
  exact Finset.single_le_sum
    (fun j _ ↦ negativePartSquare_nonneg (x j)) (Finset.mem_univ i)

theorem abs_le_sqrt_negativePartEnergy_of_neg
    {x : ι → Real} {i : ι} (hi : x i < 0) :
    |x i| ≤ Real.sqrt (negativePartEnergy x) := by
  rw [Real.le_sqrt (abs_nonneg _) (negativePartEnergy_nonneg x)]
  simpa [negativePartSquare, hi, sq_abs] using
    negativePartSquare_le_energy x i

theorem dist_nonnegativeProjection_le_sqrt (x : ι → Real) :
    dist x (nonnegativeProjection x) ≤
      Real.sqrt (negativePartEnergy x) := by
  rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
  intro i
  rw [Real.dist_eq]
  by_cases hi : x i < 0
  · rw [nonnegativeProjection_eq_zero_of_neg hi, sub_zero]
    exact abs_le_sqrt_negativePartEnergy_of_neg hi
  · simp [nonnegativeProjection, le_of_not_gt hi]

theorem negativePartEnergy_eq_zero_iff (x : ι → Real) :
    negativePartEnergy x = 0 ↔ ∀ i, 0 ≤ x i := by
  constructor
  · intro hzero i
    have hle := negativePartSquare_le_energy x i
    have heq : negativePartSquare (x i) = 0 := by
      exact le_antisymm (by simpa [hzero] using hle)
        (negativePartSquare_nonneg (x i))
    exact (negativePartSquare_eq_zero_iff (x i)).mp heq
  · intro h
    unfold negativePartEnergy
    apply Finset.sum_eq_zero
    intro i _
    exact (negativePartSquare_eq_zero_iff (x i)).mpr (h i)

/-- A `C¹` finite-dimensional vector field that points inward on the boundary
of the nonnegative orthant preserves that orthant along every supplied
forward integral curve. -/
theorem nonnegative_of_integralCurveOn
    (f : (ι → Real) → (ι → Real))
    (hf : ContDiff Real 1 f)
    (hinward : ∀ x : ι → Real, (∀ i, 0 ≤ x i) →
      ∀ i, x i = 0 → 0 ≤ f x i)
    {D : Real → (ι → Real)} {t₀ b : Real}
    (hD : IsIntegralCurveOn D (fun _ ↦ f) (Ico t₀ b))
    (hD₀ : ∀ i, 0 ≤ D t₀ i) :
    ∀ t ∈ Ico t₀ b, ∀ i, 0 ≤ D t i := by
  intro t ht i
  have hIccSubset : Icc t₀ t ⊆ Ico t₀ b := by
    intro u hu
    exact ⟨hu.1, hu.2.trans_lt ht.2⟩
  have hDcontinuous : ContinuousOn D (Icc t₀ t) := by
    intro u hu
    exact (hD u (hIccSubset hu)).continuousWithinAt.mono hIccSubset
  obtain ⟨R, hR, hRbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hDcontinuous).isBounded.exists_pos_norm_le
  have hDball : ∀ u ∈ Icc t₀ t, D u ∈ closedBall (0 : ι → Real) R := by
    intro u hu
    rw [mem_closedBall, dist_zero_right]
    exact hRbound (D u) ⟨u, hu, rfl⟩
  have hProjBall : ∀ u ∈ Icc t₀ t,
      nonnegativeProjection (D u) ∈ closedBall (0 : ι → Real) R := by
    intro u hu
    rw [mem_closedBall, dist_zero_right]
    exact (norm_nonnegativeProjection_le (D u)).trans
      (by simpa only [mem_closedBall, dist_zero_right] using hDball u hu)
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : ι → Real) R) (isCompact_closedBall _ _)
  let V : Real → Real := fun u ↦ negativePartEnergy (D u)
  let V' : Real → Real := fun u ↦
    ∑ j, (if D u j < 0 then 2 * D u j else 0) * f (D u) j
  have hVderivIco : ∀ u ∈ Ico t₀ b,
      HasDerivWithinAt V (V' u) (Ico t₀ b) u := by
    intro u hu
    have hcoord := hasDerivWithinAt_pi.mp (hD u hu)
    exact HasDerivWithinAt.fun_sum fun j _ ↦ by
      simpa [V, V', Function.comp_def] using
        (hasDerivAt_negativePartSquare (D u j)).comp_hasDerivWithinAt
          u (hcoord j)
  have hVcontinuous : ContinuousOn V (Icc t₀ t) := by
    intro u hu
    exact (hVderivIco u (hIccSubset hu)).continuousWithinAt.mono hIccSubset
  have hVright : ∀ u ∈ Ico t₀ t,
      HasDerivWithinAt V (V' u) (Ici u) u := by
    intro u hu
    have huBig : u ∈ Ico t₀ b := hIccSubset ⟨hu.1, hu.2.le⟩
    have hmono : HasDerivWithinAt V (V' u) (Ico u b) u :=
      (hVderivIco u huBig).mono (Ico_subset_Ico_left hu.1)
    simpa only [HasDerivWithinAt, nhdsWithin_Ico_eq_nhdsGE huBig.2] using hmono
  have hVbound : ∀ u ∈ Ico t₀ t,
      V' u ≤ ((Fintype.card ι : Real) * (2 * (K : Real))) * V u := by
    intro u hu
    have huIcc : u ∈ Icc t₀ t := ⟨hu.1, hu.2.le⟩
    have hVnonneg : 0 ≤ V u := negativePartEnergy_nonneg (D u)
    have hdist : dist (D u) (nonnegativeProjection (D u)) ≤ Real.sqrt (V u) := by
      exact dist_nonnegativeProjection_le_sqrt (D u)
    have hLip := hK.dist_le_mul (D u) (hDball u huIcc)
      (nonnegativeProjection (D u)) (hProjBall u huIcc)
    have hfieldDist : dist (f (D u)) (f (nonnegativeProjection (D u))) ≤
        (K : Real) * Real.sqrt (V u) :=
      hLip.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)
    have hterm : ∀ j,
        (if D u j < 0 then 2 * D u j else 0) * f (D u) j ≤
          2 * (K : Real) * V u := by
      intro j
      by_cases hj : D u j < 0
      · have hprojzero : nonnegativeProjection (D u) j = 0 :=
          nonnegativeProjection_eq_zero_of_neg hj
        have hin : 0 ≤ f (nonnegativeProjection (D u)) j :=
          hinward (nonnegativeProjection (D u))
            (nonnegativeProjection_nonneg (D u)) j hprojzero
        have hcoordDist :
            |f (D u) j - f (nonnegativeProjection (D u)) j| ≤
              dist (f (D u)) (f (nonnegativeProjection (D u))) := by
          simpa [Real.dist_eq] using
            (dist_pi_le_iff (dist_nonneg : 0 ≤
              dist (f (D u)) (f (nonnegativeProjection (D u))))).mp le_rfl j
        have hdiff :
            |f (D u) j - f (nonnegativeProjection (D u)) j| ≤
              (K : Real) * Real.sqrt (V u) := hcoordDist.trans hfieldDist
        have hx : |D u j| ≤ Real.sqrt (V u) := by
          exact abs_le_sqrt_negativePartEnergy_of_neg hj
        have hprod :
            2 * |D u j| *
                |f (D u) j - f (nonnegativeProjection (D u)) j| ≤
              2 * Real.sqrt (V u) *
                ((K : Real) * Real.sqrt (V u)) := by
          gcongr
        have hsqrt : Real.sqrt (V u) ^ 2 = V u := Real.sq_sqrt hVnonneg
        simp only [hj, if_true]
        calc
          (2 * D u j) * f (D u) j =
              (2 * D u j) * f (nonnegativeProjection (D u)) j +
                (2 * D u j) *
                  (f (D u) j - f (nonnegativeProjection (D u)) j) := by ring
          _ ≤ 0 + |(2 * D u j) *
                  (f (D u) j - f (nonnegativeProjection (D u)) j)| := by
            gcongr
            · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hin
            · exact le_abs_self _
          _ = 2 * |D u j| *
                |f (D u) j - f (nonnegativeProjection (D u)) j| := by
            rw [zero_add, abs_mul, abs_mul]
            norm_num
          _ ≤ 2 * Real.sqrt (V u) *
                ((K : Real) * Real.sqrt (V u)) := hprod
          _ = 2 * (K : Real) * V u := by
            nlinarith
      · simp only [hj, if_false, zero_mul]
        exact mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) hVnonneg
    unfold V'
    calc
      (∑ j, (if D u j < 0 then 2 * D u j else 0) * f (D u) j) ≤
          ∑ _j : ι, 2 * (K : Real) * V u :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = ((Fintype.card ι : Real) * (2 * (K : Real))) * V u := by
        simp
        ring
  have hVinitial : V t₀ = 0 := by
    exact (negativePartEnergy_eq_zero_iff (D t₀)).mpr hD₀
  let C : Real := (Fintype.card ι : Real) * (2 * (K : Real))
  have hVbound' : ∀ u ∈ Ico t₀ t, V' u ≤ C * V u + 0 := by
    intro u hu
    simpa only [C, add_zero] using hVbound u hu
  have hVle := le_gronwallBound_of_liminf_deriv_right_le
    hVcontinuous
    (fun u hu _r hr ↦ (hVright u hu).liminf_right_slope_le hr)
    (show V t₀ ≤ 0 by simp [hVinitial])
    hVbound' t ⟨ht.1, le_rfl⟩
  have hVzero : V t = 0 := by
    apply le_antisymm
    · simpa only [gronwallBound_ε0_δ0] using hVle
    · exact negativePartEnergy_nonneg (D t)
  exact (negativePartEnergy_eq_zero_iff (D t)).mp hVzero i

namespace ThreeWaveNetwork

open ArchonPhysics.CoerciveHamiltonianGlobalExistence
open ArchonPhysics.FiniteDimensionalGlobalContinuation
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad]

theorem waveKinetic_nonnegative_of_integralCurveOn
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real) (hrate : ∀ a, 0 ≤ rate a) (g : Real)
    {D : Real → (Mode → Real)} {t₀ b : Real}
    (hD : IsIntegralCurveOn D
      (fun _ ↦ waveKineticVectorField
        (networkCollisionData network frequency rate) g) (Ico t₀ b))
    (hD₀ : ∀ i, 0 ≤ D t₀ i) :
    ∀ t ∈ Ico t₀ b, ∀ i, 0 ≤ D t i := by
  exact nonnegative_of_integralCurveOn
    (waveKineticVectorField (networkCollisionData network frequency rate) g)
    (waveKineticVectorField_contDiff network frequency rate g)
    (fun x hx i hi ↦ waveKineticVectorField_nonneg_at_boundary
      network frequency rate hrate g x hx i hi)
    hD hD₀

/-- Automatic orthant invariance removes the explicit trajectory-positivity
assumption from finite-endpoint continuation. -/
theorem exists_strictForwardExtension_of_network_solution
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real) (hrate : ∀ a, 0 ≤ rate a)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) {D : Real → (Mode → Real)} {t₀ b : Real} (ht : t₀ < b)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ waveKineticVectorField
        (networkCollisionData network frequency rate) g) (Ico t₀ b))
    (hD₀ : ∀ i, 0 ≤ D t₀ i)
    {omegaMin : Real} (homegaMin : 0 < omegaMin)
    (homega : ∀ i, omegaMin ≤ frequency i) :
    ∃ (bNext : Real) (delta : Real → (Mode → Real)),
      IsStrictForwardExtension
        (waveKineticVectorField
          (networkCollisionData network frequency rate) g)
        D delta t₀ b bNext := by
  exact exists_strictForwardExtension_of_nonnegative_network_solution
    network frequency rate hresonance g ht hD
    (waveKinetic_nonnegative_of_integralCurveOn
      network frequency rate hrate g hD hD₀)
    homegaMin homega

/-- Kinetic energy is conserved for any scalar multiple of the collision
field; the scalar may subsequently depend on the current state. -/
theorem totalKineticEnergy_hasDerivWithinAt_zero_of_smulVectorField
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g a : Real) {D : Real → (Mode → Real)} {s : Set Real} {t : Real}
    (hD : HasDerivWithinAt D
      (a • waveKineticVectorField
        (networkCollisionData network frequency rate) g (D t)) s t) :
    HasDerivWithinAt (fun u ↦ totalKineticEnergy frequency (D u)) 0 s t := by
  have hcoord := hasDerivWithinAt_pi.mp hD
  have hsum : HasDerivWithinAt
      (fun u ↦ ∑ i, frequency i * D u i)
      (∑ i, frequency i *
        (a • waveKineticVectorField
          (networkCollisionData network frequency rate) g (D t)) i) s t := by
    exact HasDerivWithinAt.fun_sum fun i _ ↦ (hcoord i).const_mul (frequency i)
  apply hsum.congr_deriv
  have hzero := totalEnergySlope_eq_zero_of_resonance
    network frequency rate (D t) hresonance
  simp only [waveKineticVectorField, networkCollisionData, Pi.smul_apply,
    smul_eq_mul]
  calc
    (∑ i, frequency i * (a * (g ^ 2 * collisionVectorField network rate (D t) i))) =
        (a * g ^ 2) *
          (∑ i, frequency i * collisionVectorField network rate (D t) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      unfold totalEnergySlope weightedObservableSlope at hzero
      rw [hzero, mul_zero]

omit [Fintype Mode] in
/-- Every nonnegative initial action for a resonant finite network with
positive frequencies has an actual solution on the whole forward half-line.
The returned curve solves the untruncated kinetic equation and stays in the
nonnegative orthant for every nonnegative time. -/
theorem exists_globalForward_network_solution [Finite Mode]
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real) (hrate : ∀ a, 0 ≤ rate a)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) (action₀ : Mode → Real) (haction₀ : ∀ i, 0 ≤ action₀ i)
    {omegaMin : Real} (homegaMin : 0 < omegaMin)
    (homega : ∀ i, omegaMin ≤ frequency i) :
    ∃ D : Real → (Mode → Real), D 0 = action₀ ∧
      ∀ t : Real, 0 ≤ t →
        (∀ i, 0 ≤ D t i) ∧
          HasDerivAt D
            (waveKineticVectorField
              (networkCollisionData network frequency rate) g (D t)) t := by
  let _ : Fintype Mode := Fintype.ofFinite Mode
  let field : (Mode → Real) → (Mode → Real) :=
    waveKineticVectorField (networkCollisionData network frequency rate) g
  let initialEnergy : Real := totalKineticEnergy frequency action₀
  have hinitialEnergy : 0 ≤ initialEnergy := by
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (homegaMin.le.trans (homega i)) (haction₀ i)
  let R : Real := initialEnergy / omegaMin
  have hR : 0 ≤ R := div_nonneg hinitialEnergy homegaMin.le
  let truncated : (Mode → Real) → (Mode → Real) :=
    normCutoffVectorField field R hR
  have htruncatedContDiff : ContDiff Real 1 truncated := by
    exact normCutoffVectorField_contDiff
      (waveKineticVectorField_contDiff network frequency rate g) R hR
  have htruncatedCompact : HasCompactSupport truncated := by
    exact normCutoffVectorField_hasCompactSupport field R hR
  have htruncatedInward : ∀ x : Mode → Real, (∀ i, 0 ≤ x i) →
      ∀ i, x i = 0 → 0 ≤ truncated x i := by
    intro x hx i hi
    change 0 ≤ normCutoffBump (E := Mode → Real) R hR x * field x i
    exact mul_nonneg (normCutoffBump (E := Mode → Real) R hR).nonneg
      (waveKineticVectorField_nonneg_at_boundary
        network frequency rate hrate g x hx i hi)
  obtain ⟨D, hDzero, hD⟩ :=
    exists_global_integralCurve_of_contDiff_hasCompactSupport
      htruncatedContDiff htruncatedCompact action₀
  have hnonneg : ∀ t : Real, 0 ≤ t → ∀ i, 0 ≤ D t i := by
    intro t ht i
    have hcurve : IsIntegralCurveOn D (fun _ ↦ truncated) (Ico 0 (t + 1)) :=
      fun u _hu ↦ (hD u).hasDerivWithinAt
    have hinitial : ∀ j, 0 ≤ D 0 j := by
      simpa only [hDzero] using haction₀
    exact nonnegative_of_integralCurveOn truncated htruncatedContDiff
      htruncatedInward hcurve hinitial t ⟨ht, by linarith⟩ i
  have henergyDeriv : ∀ t : Real,
      HasDerivAt (fun u ↦ totalKineticEnergy frequency (D u)) 0 t := by
    intro t
    have hscaled : HasDerivAt D
        ((normCutoffBump (E := Mode → Real) R hR (D t)) • field (D t)) t := by
      simpa [truncated, normCutoffVectorField] using hD t
    exact (totalKineticEnergy_hasDerivWithinAt_zero_of_smulVectorField
      network frequency rate hresonance g
      (normCutoffBump (E := Mode → Real) R hR (D t))
      (s := univ) hscaled.hasDerivWithinAt).hasDerivAt Filter.univ_mem
  have henergy : ∀ t : Real,
      totalKineticEnergy frequency (D t) = initialEnergy := by
    intro t
    let energy : Real → Real := fun u ↦ totalKineticEnergy frequency (D u)
    have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0) (fun u _ ↦ (henergyDeriv u).hasDerivWithinAt)
      (fun _ _ ↦ by simp) (mem_univ (0 : Real)) (mem_univ t)
    have heq : energy t = energy 0 := by
      simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero]
        using hbound
    simpa [energy, initialEnergy, hDzero] using heq
  refine ⟨D, hDzero, fun t ht ↦ ?_⟩
  have hpositive := hnonneg t ht
  have hnorm : ‖D t‖ ≤ R := by
    have hbound := norm_le_totalKineticEnergy_div frequency (D t) hpositive
      homegaMin homega
    simpa only [R, henergy t] using hbound
  have hDtruncated := hD t
  change HasDerivAt D (normCutoffVectorField field R hR (D t)) t at hDtruncated
  rw [normCutoffVectorField_eq_of_norm_le field R hR hnorm] at hDtruncated
  exact ⟨hpositive, hDtruncated⟩

end ThreeWaveNetwork

end

end ArchonPhysics.FiniteNonnegativeOrthantInvariance
