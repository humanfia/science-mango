import ArchonPhysics.HighDimensionalPaperSpectralEntropyScaling

/-!
# Thermodynamic limits for modal-energy equipartition

This module separates three notions which are easy to conflate:

* the finite-volume normalized modal-energy `l1` error;
* a transparent tail estimate whose tolerance vanishes with system size;
* the paper's fixed spectral-entropy thresholds, which do not themselves
  tighten as the system size grows.

No microscopic tail estimate is asserted here.  Supplying one is exactly the
content of `ThermodynamicTailControl`.
-/

namespace ArchonPhysics.ThermodynamicEquipartitionLimit

open Filter Topology
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.DimensionalPaperSpectralEntropyScaling

noncomputable section

/-- The mode count genuinely grows with the lattice side.  The bare
`HighDimensionalModalEnergySource` interface deliberately allows arbitrary
finite mode types, so `side -> infinity` does not imply this property by
definition. -/
def HasThermodynamicModeGrowth
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega) : Prop :=
  Tendsto (fun side => Fintype.card (source.Mode side)) atTop atTop

/-- Formula lock for genuine thermodynamic mode growth. -/
theorem hasThermodynamicModeGrowth_iff
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega) :
    HasThermodynamicModeGrowth source <->
      Tendsto (fun side => Fintype.card (source.Mode side)) atTop atTop := by
  rfl

/-- The normalized modal-energy `l1` equipartition error of a late window. -/
def lateWindowEquipartitionError
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) (side : Nat) (g : Real) (omega : Omega) (T : Real) : Real :=
  l1Distance
    (normalizedWeights
      (lateWindowAverage (source.energy side g omega) mu T))
    (uniformWeights : source.Mode side -> Real)

/-- Formula lock for the complete normalized late-window energy error. -/
theorem lateWindowEquipartitionError_eq_sum_abs
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) (side : Nat) (g : Real) (omega : Omega) (T : Real) :
    lateWindowEquipartitionError source mu side g omega T =
      ∑ i : source.Mode side,
        |lateWindowAverage (source.energy side g omega) mu T i /
              totalWeight
                (lateWindowAverage (source.energy side g omega) mu T) -
            (Fintype.card (source.Mode side) : Real)⁻¹| := by
  rfl

/-- The finite modal-energy equipartition error is always nonnegative. -/
theorem lateWindowEquipartitionError_nonneg
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) (side : Nat) (g : Real) (omega : Omega) (T : Real) :
    0 <= lateWindowEquipartitionError source mu side g omega T := by
  unfold lateWindowEquipartitionError l1Distance
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- A finite late window is physically admissible when its averaging interval
is nondegenerate, the supplied raw modal energies are pointwise nonnegative,
and the averaged total energy is strictly positive.  The coupling `g` and the
sample `omega` are fixed data of this finite-volume observation. -/
structure PhysicalLateWindow
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (mu : Real) (side : Nat) (g : Real) (omega : Omega) (T : Real) : Prop where
  mu_nonneg : 0 <= mu
  mu_lt_one : mu < 1
  time_pos : 0 < T
  energy_nonneg : forall t i, 0 <= source.energy side g omega t i
  totalWeight_pos : 0 < totalWeight
    (lateWindowAverage (source.energy side g omega) mu T)

/-- Physical admissibility makes the normalized late-window modal weights a
probability vector. -/
theorem PhysicalLateWindow.sum_normalizedWeights_eq_one
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    {source : HighDimensionalModalEnergySource kind Omega}
    {mu : Real} {side : Nat} {g : Real} {omega : Omega} {T : Real}
    (hphysical : PhysicalLateWindow source mu side g omega T) :
    ∑ i : source.Mode side,
        normalizedWeights
          (lateWindowAverage (source.energy side g omega) mu T) i = 1 := by
  exact sum_normalizedWeights _ hphysical.totalWeight_pos

/-- Under the physical late-window conditions, the normalized modal-energy
error is bounded by the diameter `2` of the finite probability simplex. -/
theorem PhysicalLateWindow.lateWindowEquipartitionError_le_two
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    {source : HighDimensionalModalEnergySource kind Omega}
    {mu : Real} {side : Nat} {g : Real} {omega : Omega} {T : Real}
    (hphysical : PhysicalLateWindow source mu side g omega T) :
    lateWindowEquipartitionError source mu side g omega T <= 2 := by
  have haverageNonneg : forall i,
      0 <= lateWindowAverage (source.energy side g omega) mu T i :=
    lateWindowAverage_nonneg _ _ _ hphysical.mu_nonneg
      hphysical.mu_lt_one hphysical.time_pos hphysical.energy_nonneg
  classical
  rcases isEmpty_or_nonempty (source.Mode side) with hmode | hmode
  · let _ := hmode
    have hpositive := hphysical.totalWeight_pos
    simp [totalWeight] at hpositive
  · let _ := hmode
    exact l1Distance_normalized_uniform_le_two _ haverageNonneg
      hphysical.totalWeight_pos

/-- Complete universal range of the physical finite-volume equipartition
error. -/
theorem PhysicalLateWindow.lateWindowEquipartitionError_bounds
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    {source : HighDimensionalModalEnergySource kind Omega}
    {mu : Real} {side : Nat} {g : Real} {omega : Omega} {T : Real}
    (hphysical : PhysicalLateWindow source mu side g omega T) :
    0 <= lateWindowEquipartitionError source mu side g omega T /\
      lateWindowEquipartitionError source mu side g omega T <= 2 := by
  exact ⟨lateWindowEquipartitionError_nonneg _ _ _ _ _ _,
    hphysical.lateWindowEquipartitionError_le_two⟩

/-- A transparent tail-control certificate.  At size `N`, every observation
after `settlingBound N` has nonnegative error bounded by `tolerance N`, and
the tolerance vanishes in the thermodynamic limit. -/
structure ThermodynamicTailControl
    (error : Nat -> Real -> Real) where
  tolerance : Nat -> Real
  settlingBound : Nat -> Real
  tolerance_nonneg : forall N, 0 <= tolerance N
  tolerance_tendsto_zero : Tendsto tolerance atTop (nhds 0)
  settlingBound_nonneg : forall N, 0 <= settlingBound N
  error_tail : forall N t, settlingBound N <= t ->
    0 <= error N t /\ error N t <= tolerance N

/-- Along every growing-volume path observed after its certified settling
bound, the equipartition error tends to zero. -/
theorem ThermodynamicTailControl.error_tendsto_zero_along
    {error : Nat -> Real -> Real}
    (control : ThermodynamicTailControl error)
    (side : Nat -> Nat) (observationTime : Nat -> Real)
    (hside : Tendsto side atTop atTop)
    (hobservation : forall j,
      control.settlingBound (side j) <= observationTime j) :
    Tendsto
      (fun j => error (side j) (observationTime j))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun j =>
      (control.error_tail (side j) (observationTime j)
        (hobservation j)).1
  · exact Filter.Eventually.of_forall fun j =>
      (control.error_tail (side j) (observationTime j)
        (hobservation j)).2
  · exact control.tolerance_tendsto_zero.comp hside

/-- Direct epsilon form of thermodynamic tail control: for every positive
error band, every sufficiently large volume remains in that band at every
time after its size-dependent settling bound. -/
theorem ThermodynamicTailControl.eventually_error_lt_on_every_settled_tail
    {error : Nat -> Real -> Real}
    (control : ThermodynamicTailControl error) :
    forall epsilon : Real, 0 < epsilon ->
      exists N0 : Nat, forall N : Nat, N0 <= N -> forall t : Real,
        control.settlingBound N <= t ->
          0 <= error N t /\ error N t < epsilon := by
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ :=
    Metric.tendsto_atTop.mp control.tolerance_tendsto_zero epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN t ht
  have htail := control.error_tail N t ht
  have htolerance := hN0 N hN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (control.tolerance_nonneg N)] at htolerance
  exact ⟨htail.1, htail.2.trans_lt htolerance⟩

/-- Source-specialized thermodynamic tail theorem.  The lattice-kind type has
only the supported two- and three-dimensional families, while `g` and
`omega` remain fixed along the volume path. -/
theorem highDimensionalSource_lateWindowEquipartitionError_tendsto_zero_along
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (_hmodeGrowth : HasThermodynamicModeGrowth source)
    (mu g : Real) (omega : Omega)
    (control : ThermodynamicTailControl
      (fun side T =>
        lateWindowEquipartitionError source mu side g omega T))
    (side : Nat -> Nat) (observationTime : Nat -> Real)
    (hside : Tendsto side atTop atTop)
    (hobservation : forall j,
      control.settlingBound (side j) <= observationTime j) :
    Tendsto
      (fun j => lateWindowEquipartitionError source mu (side j) g omega
        (observationTime j))
      atTop (nhds 0) :=
  control.error_tendsto_zero_along side observationTime hside hobservation

/-- Physical source endpoint for the thermodynamic diagonal limit.  A single
supplied coupling `g` and sample `omega` are held fixed while the side and mode
count grow and the observation time lies beyond the certified late-time
bound.  This is not a fixed-energy-density limit: no size-dependent energy
density is introduced or inferred.  Physical validity at every observation
both normalizes the modal weights and places every finite-volume error in the
universal interval `[0, 2]`. -/
theorem highDimensionalSource_physical_lateWindowEquipartitionError_limit
    {kind : HighDimensionalLatticeKind} {Omega : Type}
    (source : HighDimensionalModalEnergySource kind Omega)
    (hmodeGrowth : HasThermodynamicModeGrowth source)
    (mu g : Real) (omega : Omega)
    (control : ThermodynamicTailControl
      (fun side T =>
        lateWindowEquipartitionError source mu side g omega T))
    (side : Nat -> Nat) (observationTime : Nat -> Real)
    (hside : Tendsto side atTop atTop)
    (hobservation : forall j,
      control.settlingBound (side j) <= observationTime j)
    (hphysical : forall j,
      PhysicalLateWindow source mu (side j) g omega (observationTime j)) :
    Tendsto
        (fun j => lateWindowEquipartitionError source mu (side j) g omega
          (observationTime j))
        atTop (nhds 0) /\
      forall j,
        0 <= lateWindowEquipartitionError source mu (side j) g omega
            (observationTime j) /\
          lateWindowEquipartitionError source mu (side j) g omega
            (observationTime j) <= 2 := by
  constructor
  · exact
      highDimensionalSource_lateWindowEquipartitionError_tendsto_zero_along
        source hmodeGrowth mu g omega control side observationTime hside
          hobservation
  · intro j
    exact (hphysical j).lateWindowEquipartitionError_bounds

/-- Every available high-dimensional lattice tag is two- or
three-dimensional. -/
theorem highDimensionalLatticeKind_dimension_eq_two_or_three
    (kind : HighDimensionalLatticeKind) :
    kind.dimension = 2 \/ kind.dimension = 3 := by
  cases kind <;> simp [HighDimensionalLatticeKind.dimension]

/-- A size-independent real threshold tends to one exactly when it already
equals one. -/
theorem constant_threshold_tendsto_one_iff (threshold : Real) :
    Tendsto (fun _ : Nat => threshold) atTop (nhds 1) <-> threshold = 1 := by
  constructor
  · intro hthreshold
    exact tendsto_nhds_unique
      (tendsto_const_nhds :
        Tendsto (fun _ : Nat => threshold) atTop (nhds threshold))
      hthreshold
  · rintro rfl
    exact tendsto_const_nhds

/-- The published `0.65` threshold is not a shrinking thermodynamic
threshold. -/
theorem not_tendsto_constant_threshold_sixtyFivePercent_to_one :
    ¬ Tendsto (fun _ : Nat => (0.65 : Real)) atTop (nhds 1) := by
  intro h
  have heq : (0.65 : Real) = 1 :=
    (constant_threshold_tendsto_one_iff (0.65 : Real)).mp h
  norm_num at heq

/-- The published `0.95` threshold is not a shrinking thermodynamic
threshold. -/
theorem not_tendsto_constant_threshold_ninetyFivePercent_to_one :
    ¬ Tendsto (fun _ : Nat => (0.95 : Real)) atTop (nhds 1) := by
  intro h
  have heq : (0.95 : Real) = 1 :=
    (constant_threshold_tendsto_one_iff (0.95 : Real)).mp h
  norm_num at heq

/-- Spectral-entropy threshold associated with a requested `l1` tolerance.
Pinsker's inequality, intentionally separate from this module, motivates the
normalization `exp (-delta^2 / 2)`. -/
def shrinkingXiThreshold (delta : Real) : Real :=
  Real.exp (-(delta ^ 2) / 2)

/-- Vanishing equipartition tolerances give spectral-entropy thresholds which
tend to one. -/
theorem shrinkingXiThreshold_tendsto_one
    {alpha : Type} {l : Filter alpha} (delta : alpha -> Real)
    (hdelta : Tendsto delta l (nhds 0)) :
    Tendsto (fun i => shrinkingXiThreshold (delta i)) l (nhds 1) := by
  have hcontinuous : Continuous shrinkingXiThreshold := by
    unfold shrinkingXiThreshold
    fun_prop
  change Tendsto ((Function.comp shrinkingXiThreshold delta)) l (nhds 1)
  convert (hcontinuous.tendsto 0).comp hdelta using 1
  simp [shrinkingXiThreshold]

end

end ArchonPhysics.ThermodynamicEquipartitionLimit
