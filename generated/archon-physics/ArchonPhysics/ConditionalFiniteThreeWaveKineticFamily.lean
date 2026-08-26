import ArchonPhysics.FiniteNonnegativeOrthantInvariance
import ArchonPhysics.MonotoneKineticCrossing
import ArchonPhysics.LateWindowRescaling
import ArchonPhysics.WeightedDegenerateRelaxation

/-!
# Conditional finite three-wave kinetic family

This is the faithful aggregation layer for the effective kinetic family.  It
packages a finite `1 ↔ 2 + 3` collision network, constructs an untruncated
global forward solution from every nonnegative initial action, records
nonnegativity and exact energy conservation, and transports the selected
unit-coupling solution by the exact time change `tau = g² t`.

The final crossing is deliberately conditional.  The fields called
`kernelCoercivity_strictAnti` and `relaxationToEquipartition` are the missing
analytic relaxation statements for the concrete collision kernel; this file
does not prove them for the frozen random lattice.
-/

namespace ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily

open Filter MeasureTheory Set
open ArchonPhysics
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteThreeWaveCollisionNetwork
open ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
open ArchonPhysics.FiniteNonnegativeOrthantInvariance.ThreeWaveNetwork

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad]

/-- Concrete finite collision data together with precisely the hypotheses used
to construct a nonnegative global forward kinetic trajectory. -/
structure FiniteCollisionModel (Mode Triad : Type)
    [Fintype Mode] [DecidableEq Mode] [Fintype Triad] where
  network : Network Mode Triad
  frequency : Mode → Real
  rate : Triad → Real
  omegaMin : Real
  rate_nonneg : ∀ a, 0 ≤ rate a
  resonance : ∀ a, frequency (network.mode₁ a) =
    frequency (network.mode₂ a) + frequency (network.mode₃ a)
  omegaMin_pos : 0 < omegaMin
  frequency_lower : ∀ i, omegaMin ≤ frequency i

/-- The `CollisionData` represented by the finite network. -/
def FiniteCollisionModel.collisionData
    (model : FiniteCollisionModel Mode Triad) : CollisionData Mode :=
  networkCollisionData model.network model.frequency model.rate

@[simp] theorem FiniteCollisionModel.collisionData_omega
    (model : FiniteCollisionModel Mode Triad) (i : Mode) :
    model.collisionData.omega i = model.frequency i := by
  rfl

@[simp] theorem FiniteCollisionModel.collisionData_collision
    (model : FiniteCollisionModel Mode Triad) (action : Mode → Real) :
    model.collisionData.collision action =
      collisionVectorField model.network model.rate action := by
  rfl

/-- A selected solution on the whole forward half-line, including the
properties needed by downstream observable and scaling arguments. -/
structure GlobalForwardCertificate
    (model : FiniteCollisionModel Mode Triad) (g : Real)
    (action₀ : Mode → Real) where
  trajectory : Real → (Mode → Real)
  initial : trajectory 0 = action₀
  nonnegative : ∀ t, 0 ≤ t → ∀ i, 0 ≤ trajectory t i
  equation : ∀ t, 0 ≤ t → HasDerivAt trajectory
    (waveKineticVectorField model.collisionData g (trajectory t)) t
  energy_conserved : ∀ t, 0 ≤ t →
    totalKineticEnergy model.frequency (trajectory t) =
      totalKineticEnergy model.frequency action₀

/-- The existing global-existence and orthant-invariance theorems construct a
certificate for every nonnegative initial action. -/
theorem exists_globalForwardCertificate
    (model : FiniteCollisionModel Mode Triad) (g : Real)
    (action₀ : Mode → Real) (haction₀ : ∀ i, 0 ≤ action₀ i) :
    ∃ _certificate : GlobalForwardCertificate model g action₀, True := by
  obtain ⟨D, hDzero, hD⟩ := exists_globalForward_network_solution
    model.network model.frequency model.rate model.rate_nonneg model.resonance
    g action₀ haction₀ model.omegaMin_pos model.frequency_lower
  have henergy : ∀ t, 0 ≤ t →
      totalKineticEnergy model.frequency (D t) =
        totalKineticEnergy model.frequency action₀ := by
    intro t ht
    have hcurve : IsIntegralCurveOn D
        (fun _ ↦ waveKineticVectorField model.collisionData g) (Icc 0 t) := by
      intro u hu
      exact (hD u hu.1).2.hasDerivWithinAt
    have heq := totalKineticEnergy_eq_of_integralCurveOn
      model.network model.frequency model.rate model.resonance g
      (convex_Icc 0 t) hcurve (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
    simpa only [hDzero] using heq.symm
  refine ⟨⟨D, hDzero, ?_, ?_, henergy⟩, trivial⟩
  · intro t ht i
    exact (hD t ht).1 i
  · intro t ht
    exact (hD t ht).2

/-- The modal-energy path associated with a selected forward solution. -/
def GlobalForwardCertificate.modalEnergyPath
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀) :
    Real → Mode → Real :=
  fun t ↦ modalEnergy model.collisionData (certificate.trajectory t)

/-- Positive-time modal energies are nonnegative. -/
theorem GlobalForwardCertificate.modalEnergy_nonnegative
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀)
    {t : Real} (ht : 0 ≤ t) (i : Mode) :
    0 ≤ certificate.modalEnergyPath t i := by
  exact mul_nonneg
    (model.omegaMin_pos.le.trans (model.frequency_lower i))
    (certificate.nonnegative t ht i)

/-- The selected trajectory is continuous on the forward half-line. -/
theorem GlobalForwardCertificate.continuousOn_nonnegative
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀) :
    ContinuousOn certificate.trajectory (Ici 0) := by
  intro t ht
  exact (certificate.equation t ht).continuousAt.continuousWithinAt

/-- Every modal-energy coordinate is interval integrable on a nonnegative
ordered time interval. -/
theorem GlobalForwardCertificate.modalEnergy_intervalIntegrable
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀)
    {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) (i : Mode) :
    IntervalIntegrable (fun t ↦ modalEnergy model.collisionData
      (certificate.trajectory t) i) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have hD : ContinuousAt certificate.trajectory t :=
    (certificate.equation t (ha.trans ht.1)).continuousAt
  have hcoord : ContinuousAt (fun u ↦ certificate.trajectory u i) t :=
    (continuous_apply i).continuousAt.comp hD
  exact (continuousAt_const.mul hcoord).continuousWithinAt

/-- Energy conservation identifies every positive late-window total exactly
with the initial total energy. -/
theorem GlobalForwardCertificate.lateWindowTotal_eq_initialEnergy
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    totalWeight (lateWindowKineticEnergy model.collisionData
      certificate.trajectory mu T) =
      totalKineticEnergy model.frequency action₀ := by
  have hinterval : mu * T ≤ T := by
    have hbound := mul_le_mul_of_nonneg_right (le_of_lt hmuOne) hT.le
    simpa only [one_mul] using hbound
  have hmodeInt : ∀ i, IntervalIntegrable
      (fun t ↦ model.frequency i * certificate.trajectory t i)
      volume (mu * T) T := by
    intro i
    simpa only [FiniteCollisionModel.collisionData_omega,
      modalEnergy_apply] using
      certificate.modalEnergy_intervalIntegrable
        (mul_nonneg hmu hT.le) hinterval i
  have hintegral :
      (∫ t in mu * T..T,
        ∑ i, model.frequency i * certificate.trajectory t i) =
      ∫ _t in mu * T..T,
        totalKineticEnergy model.frequency action₀ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hinterval] at ht
    exact certificate.energy_conserved t
      ((mul_nonneg hmu hT.le).trans ht.1)
  unfold totalWeight lateWindowKineticEnergy
    EquipartitionEntropy.lateWindowAverage
  simp only [modalEnergy_apply, FiniteCollisionModel.collisionData_omega]
  rw [← Finset.mul_sum]
  rw [← intervalIntegral.integral_finsetSum
    (fun i _hi ↦ hmodeInt i)]
  rw [hintegral, intervalIntegral.integral_const]
  have hmu_ne : 1 - mu ≠ 0 := ne_of_gt (sub_pos.mpr hmuOne)
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp [hmu_ne, hT_ne] ; ring

/-- A positive late-window total normalizes the modal-energy weights to a
probability vector. -/
theorem GlobalForwardCertificate.sum_normalizedLateWindowEnergy_eq_one
    {model : FiniteCollisionModel Mode Triad} {g : Real}
    {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model g action₀)
    (mu T : Real)
    (hpositive : 0 < totalWeight
      (lateWindowKineticEnergy model.collisionData certificate.trajectory mu T)) :
    ∑ i, normalizedLateWindowKineticEnergy
      model.collisionData certificate.trajectory mu T i = 1 := by
  exact sum_normalizedLateWindowKineticEnergy
    model.collisionData certificate.trajectory mu T hpositive

/-- The selected unit-coupling trajectory transported by `tau = g² t`. -/
def GlobalForwardCertificate.rescaledTrajectory
    {model : FiniteCollisionModel Mode Triad} {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model 1 action₀) (g : Real) :
    Real → (Mode → Real) :=
  fun t ↦ certificate.trajectory (g ^ 2 * t)

/-- Exact rescaling constructs a genuine nonnegative global forward solution
at coupling `g`; uniqueness is not smuggled in as an assumption. -/
def GlobalForwardCertificate.rescale
    {model : FiniteCollisionModel Mode Triad} {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model 1 action₀) (g : Real) :
    GlobalForwardCertificate model g action₀ where
  trajectory := certificate.rescaledTrajectory g
  initial := by simp [GlobalForwardCertificate.rescaledTrajectory, certificate.initial]
  nonnegative := by
    intro t ht i
    exact certificate.nonnegative (g ^ 2 * t)
      (mul_nonneg (sq_nonneg g) ht) i
  equation := by
    intro t ht
    change HasDerivAt (fun s : Real => certificate.trajectory (g ^ 2 * s))
      (waveKineticVectorField model.collisionData g
        (certificate.trajectory (g ^ 2 * t))) t
    have hunit := certificate.equation (g ^ 2 * t)
      (mul_nonneg (sq_nonneg g) ht)
    apply hasDerivAt_pi.mpr
    intro i
    have hcoord := hasDerivAt_pi.mp hunit i
    simpa [waveKineticVectorField, Function.comp_def] using
      hcoord.scomp t (hasDerivAt_const_mul (g ^ 2))
  energy_conserved := by
    intro t ht
    exact certificate.energy_conserved (g ^ 2 * t)
      (mul_nonneg (sq_nonneg g) ht)

@[simp] theorem GlobalForwardCertificate.rescale_trajectory
    {model : FiniteCollisionModel Mode Triad} {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model 1 action₀)
    (g t : Real) :
    (certificate.rescale g).trajectory t =
      certificate.trajectory (g ^ 2 * t) := by
  rfl

variable [Nonempty Mode]

/-- The normalized late-window kinetic distance obeys the same exact `g²`
time change as the selected trajectory. -/
theorem GlobalForwardCertificate.kineticEquipartitionDistance_rescale
    {model : FiniteCollisionModel Mode Triad} {action₀ : Mode → Real}
    (certificate : GlobalForwardCertificate model 1 action₀)
    (g : Real) (hg : g ≠ 0) (mu T : Real)
    (hmu_nonnegative : 0 ≤ mu) (hmu_less_one : mu < 1) (hT : 0 < T) :
    kineticEquipartitionDistance model.collisionData
        (certificate.rescale g).trajectory mu T =
      kineticEquipartitionDistance model.collisionData
        certificate.trajectory mu (g ^ 2 * T) := by
  have hscaled_nonnegative : 0 ≤ g ^ 2 * T :=
    mul_nonneg (sq_nonneg g) hT.le
  have hlower_nonnegative : 0 ≤ mu * (g ^ 2 * T) :=
    mul_nonneg hmu_nonnegative hscaled_nonnegative
  have hlower_le : mu * (g ^ 2 * T) ≤ g ^ 2 * T := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_of_lt hmu_less_one)
        hscaled_nonnegative
  have hrescale : ∀ t i,
      modalEnergy model.collisionData ((certificate.rescale g).trajectory t) i =
        modalEnergy model.collisionData
          (certificate.trajectory (g ^ 2 * t)) i := by
    intro t i
    rfl
  have hintegrable : ∀ i, IntervalIntegrable
      (fun tau ↦ modalEnergy model.collisionData
        (certificate.trajectory tau) i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T) := by
    intro i
    exact certificate.modalEnergy_intervalIntegrable
      hlower_nonnegative hlower_le i
  simpa [kineticEquipartitionDistance, normalizedLateWindowKineticEnergy,
    lateWindowKineticEnergy] using
    (LateWindowRescaling.l1Distance_lateWindowAverage_rescaling
      (fun t ↦ modalEnergy model.collisionData
        ((certificate.rescale g).trajectory t))
      (fun tau ↦ modalEnergy model.collisionData
        (certificate.trajectory tau))
      mu T g hg hmu_less_one hT hrescale hintegrable)

/-- The unresolved analytic input for a fixed finite collision kernel.  The
two named fields are assumptions, not consequences of the network algebra. -/
structure AnalyticRelaxationContracts
    (model : FiniteCollisionModel Mode Triad)
    (D : Real → (Mode → Real)) (mu delta : Real) : Prop where
  mu_nonnegative : 0 ≤ mu
  mu_less_one : mu < 1
  threshold_positive : 0 < delta
  threshold_below_initial :
    delta < kineticEquipartitionProfile model.collisionData D mu 0
  distance_continuous : ContinuousOn
    (kineticEquipartitionProfile model.collisionData D mu) (Ici 0)
  /-- Missing kernel coercivity, expressed as strict decay of the actual
  normalized late-window observable. -/
  kernelCoercivity_strictAnti : StrictAntiOn
    (kineticEquipartitionProfile model.collisionData D mu) (Ici 0)
  /-- Missing relaxation theorem for the actual finite collision evolution. -/
  relaxationToEquipartition : Tendsto
    (kineticEquipartitionProfile model.collisionData D mu) atTop (nhds 0)

/-- The explicit analytic contracts produce a unique positive threshold root
and the robust margins needed by the microscopic transfer family. -/
theorem AnalyticRelaxationContracts.existsUnique_robustCrossing
    {model : FiniteCollisionModel Mode Triad}
    {D : Real → (Mode → Real)} {mu delta : Real}
    (contracts : AnalyticRelaxationContracts model D mu delta) :
    ∃! tauStar, 0 < tauStar ∧
      kineticEquipartitionProfile model.collisionData D mu tauStar = delta ∧
      RobustKineticEquipartitionCrossing
        model.collisionData D mu delta tauStar := by
  exact existsUnique_robustKineticFirstCrossing_of_monotone_decay
    contracts.distance_continuous contracts.kernelCoercivity_strictAnti
    contracts.threshold_positive contracts.threshold_below_initial
    contracts.relaxationToEquipartition

/-- The complete conditional F2 endpoint.  Its global flow is constructed;
only `relaxation` contains unresolved analytic kernel information. -/
structure ConditionalF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (action₀ : Mode → Real) (mu delta : Real) where
  unitFlow : GlobalForwardCertificate model 1 action₀
  initialEnergy_positive : 0 < totalKineticEnergy model.frequency action₀
  relaxation : AnalyticRelaxationContracts
    model unitFlow.trajectory mu delta
  tauStar : Real
  tauStar_positive : 0 < tauStar
  at_threshold : kineticEquipartitionProfile model.collisionData
    unitFlow.trajectory mu tauStar = delta
  robust_crossing : RobustKineticEquipartitionCrossing model.collisionData
    unitFlow.trajectory mu delta tauStar

/-- Once the explicitly named relaxation contract is supplied for the
constructed trajectory, the conditional F2 certificate exists. -/
theorem exists_conditionalF2Certificate
    (model : FiniteCollisionModel Mode Triad)
    (action₀ : Mode → Real) (haction₀ : ∀ i, 0 ≤ action₀ i)
    (hinitialEnergy : 0 < totalKineticEnergy model.frequency action₀)
    (mu delta : Real)
    (hcontracts : ∀ flow : GlobalForwardCertificate model 1 action₀,
      AnalyticRelaxationContracts model flow.trajectory mu delta) :
    ∃ _certificate : ConditionalF2Certificate model action₀ mu delta, True := by
  obtain ⟨flow, _⟩ := exists_globalForwardCertificate model 1 action₀ haction₀
  let contracts := hcontracts flow
  obtain ⟨tauStar, htau, _hunique⟩ := contracts.existsUnique_robustCrossing
  exact ⟨⟨flow, hinitialEnergy, contracts, tauStar,
    htau.1, htau.2.1, htau.2.2⟩, trivial⟩

/-- For every nonzero coupling the conditional certificate supplies an exact
rescaled forward solution and identifies the physical threshold time
algebraically as `tauStar / g²`, provided the observable rescaling identity is
available.  The latter is proved separately below. -/
theorem ConditionalF2Certificate.rescaledFlow_spec
    {model : FiniteCollisionModel Mode Triad}
    {action₀ : Mode → Real} {mu delta : Real}
    (certificate : ConditionalF2Certificate model action₀ mu delta)
    (g t : Real) (ht : 0 ≤ t) :
    (certificate.unitFlow.rescale g).trajectory t =
      certificate.unitFlow.trajectory (g ^ 2 * t) ∧
    totalKineticEnergy model.frequency
        ((certificate.unitFlow.rescale g).trajectory t) =
      totalKineticEnergy model.frequency action₀ := by
  constructor
  · rfl
  · exact (certificate.unitFlow.rescale g).energy_conserved t ht

/-- At nonzero coupling, the exact physical threshold time is
`tauStar / g²`; no asymptotic proportionality symbol is used. -/
theorem ConditionalF2Certificate.physicalThreshold_at_g
    {model : FiniteCollisionModel Mode Triad}
    {action₀ : Mode → Real} {mu delta : Real}
    (certificate : ConditionalF2Certificate model action₀ mu delta)
    (g : Real) (hg : g ≠ 0) :
    0 < certificate.tauStar / g ^ 2 ∧
      kineticEquipartitionDistance model.collisionData
        (certificate.unitFlow.rescale g).trajectory mu
        (certificate.tauStar / g ^ 2) = delta := by
  have hgsq : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hphysical : 0 < certificate.tauStar / g ^ 2 :=
    div_pos certificate.tauStar_positive hgsq
  have hscale : g ^ 2 * (certificate.tauStar / g ^ 2) =
      certificate.tauStar := by
    field_simp [pow_ne_zero 2 hg]
  refine ⟨hphysical, ?_⟩
  calc
    kineticEquipartitionDistance model.collisionData
        (certificate.unitFlow.rescale g).trajectory mu
        (certificate.tauStar / g ^ 2) =
      kineticEquipartitionDistance model.collisionData
        certificate.unitFlow.trajectory mu
        (g ^ 2 * (certificate.tauStar / g ^ 2)) :=
      certificate.unitFlow.kineticEquipartitionDistance_rescale
        g hg mu (certificate.tauStar / g ^ 2)
        certificate.relaxation.mu_nonnegative
        certificate.relaxation.mu_less_one hphysical
    _ = kineticEquipartitionProfile model.collisionData
        certificate.unitFlow.trajectory mu certificate.tauStar := by
      rw [hscale]
      rfl
    _ = delta := certificate.at_threshold

/-- Degenerate positive rates still give a finite weighted-error crossing;
this exposes the dominated-convergence alternative to a uniform spectral
gap, while leaving the comparison with the actual kinetic distance explicit. -/
theorem weightedDegenerateError_crosses
    {Alpha : Type*} [MeasurableSpace Alpha]
    (measure : Measure Alpha) (rate error : Alpha → Real)
    (hrate_measurable : Measurable rate)
    (herror_integrable : Integrable error measure)
    (hrate_nonnegative : ∀ᵐ x ∂measure, 0 ≤ rate x)
    (hrate_positive : ∀ᵐ x ∂measure, 0 < rate x)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ n : Nat,
      WeightedDegenerateRelaxation.weightedDecayIntegral
        measure rate error n < delta := by
  exact WeightedDegenerateRelaxation.exists_weightedDecayIntegral_lt
    measure rate error hrate_measurable herror_integrable
    hrate_nonnegative hrate_positive hdelta

end

end ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
