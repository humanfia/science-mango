import ArchonPhysics.CoerciveLatticeEnergy
import ArchonPhysics.ConcreteHamiltonGradients
import ArchonPhysics.TranslationReducedCoercivity
import ArchonPhysics.FiniteDimensionalGlobalContinuation

/-!
# Continuation for the translation-reduced coercive Hamiltonian

For nonuniform positive masses, the invariant translation gauge is the
mass-weighted position condition `∑ᵢ mᵢ qᵢ = 0`, paired with zero total
canonical momentum `∑ᵢ pᵢ = 0`.  This module places the explicit stabilized
Hamilton vector field on that finite-dimensional reduced phase space.

The concrete gradient identities prove energy conservation along every
integral curve.  Coercivity and the reduced Poincare estimate then make every
finite energy shell bounded, so the general finite-dimensional continuation
criterion rules out a finite maximal endpoint.  No global solution is used as
an input.
-/

namespace ArchonPhysics.CoerciveHamiltonianContinuation

open Filter Set
open CoerciveHamiltonianPhyslib ConcreteHamiltonGradients
open CoerciveLatticeEnergy TranslationReducedCoercivity
open FiniteDimensionalGlobalContinuation
open InnerProductSpace
open scoped NNReal Topology

noncomputable section

/-- Coordinate sum on the Euclidean finite configuration space. -/
def hilbertConfigurationSumLinearMap (N : Nat) [NeZero N] :
    HilbertConfiguration N →ₗ[Real] Real where
  toFun q := ∑ i, q i
  map_add' q r := by simp [Finset.sum_add_distrib]
  map_smul' c q := by simp [Finset.mul_sum]

@[simp] theorem hilbertConfigurationSumLinearMap_apply
    {N : Nat} [NeZero N] (q : HilbertConfiguration N) :
    hilbertConfigurationSumLinearMap N q = ∑ i, q i := by
  rfl

/-- Mass-weighted coordinate sum, i.e. the center-of-mass numerator. -/
def massWeightedConfigurationSumLinearMap {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : HilbertConfiguration N →ₗ[Real] Real where
  toFun q := ∑ i, m.mass i * q i
  map_add' q r := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem massWeightedConfigurationSumLinearMap_apply
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : HilbertConfiguration N) :
    massWeightedConfigurationSumLinearMap m q = ∑ i, m.mass i * q i := by
  rfl

/-- Translation gauge adapted to nonuniform masses. -/
def ReducedPositionSpace {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Submodule Real (HilbertConfiguration N) :=
  LinearMap.ker (massWeightedConfigurationSumLinearMap m)

/-- Zero-total-momentum sector, invariant under internal bond forces. -/
def ReducedMomentumSpace (N : Nat) [NeZero N] :
    Submodule Real (HilbertConfiguration N) :=
  LinearMap.ker (hilbertConfigurationSumLinearMap N)

/-- Translation-reduced phase space, ordered as `(q,p)`. -/
abbrev ReducedPhaseSpace {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :=
  ReducedPositionSpace m × ReducedMomentumSpace N

theorem mem_reducedPositionSpace_iff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N) :
    q ∈ ReducedPositionSpace m ↔ ∑ i, m.mass i * q i = 0 := by
  simp [ReducedPositionSpace]

theorem mem_reducedMomentumSpace_iff {N : Nat} [NeZero N]
    (p : HilbertConfiguration N) :
    p ∈ ReducedMomentumSpace N ↔ ∑ i, p i = 0 := by
  simp [ReducedMomentumSpace]

/-- Every bond direction has zero total coordinate sum. -/
theorem sum_bondDirection {N : Nat} [NeZero N] (i : Lattice.Site N) :
    ∑ j : Lattice.Site N, bondDirection i j = 0 := by
  simp [bondDirection]

/-- A bond direction regarded as a reduced momentum vector. -/
def reducedBondDirection {N : Nat} [NeZero N] (i : Lattice.Site N) :
    ReducedMomentumSpace N :=
  ⟨bondDirection i, (mem_reducedMomentumSpace_iff _).2 (sum_bondDirection i)⟩

/-- A bond functional restricted to the mass-weighted position gauge. -/
def reducedBondFunctional {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (i : Lattice.Site N) :
    ReducedPositionSpace m →L[Real] Real :=
  (bondFunctional i).comp (ReducedPositionSpace m).subtypeL

@[simp] theorem reducedBondFunctional_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (q : ReducedPositionSpace m) :
    reducedBondFunctional m i q =
      Lattice.forwardDifference
        (asConfiguration (q : HilbertConfiguration N)) i := by
  simp [reducedBondFunctional]

/-- The concrete potential gradient with its zero-total-momentum certificate. -/
def reducedPotentialGradient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (q : ReducedPositionSpace m) : ReducedMomentumSpace N :=
  ∑ i : Lattice.Site N,
    potentialDerivative kappa beta g (reducedBondFunctional m i q) •
      reducedBondDirection i

@[simp] theorem reducedPotentialGradient_coe {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (q : ReducedPositionSpace m) :
    (reducedPotentialGradient m kappa beta g q : HilbertConfiguration N) =
      potentialGradient kappa beta g (q : HilbertConfiguration N) := by
  ext j
  simp [reducedPotentialGradient, potentialGradient, reducedBondDirection]

/-- Inverse-mass velocity preserves the mass-weighted position gauge exactly
when total canonical momentum is zero. -/
def reducedVelocity {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : ReducedMomentumSpace N) :
    ReducedPositionSpace m := by
  refine ⟨inverseMassMomentum m (p : HilbertConfiguration N), ?_⟩
  rw [mem_reducedPositionSpace_iff]
  have hp : ∑ i : Lattice.Site N, (p : HilbertConfiguration N) i = 0 :=
    (mem_reducedMomentumSpace_iff _).1 p.property
  calc
    (∑ i : Lattice.Site N,
        m.mass i * inverseMassMomentum m (p : HilbertConfiguration N) i) =
        ∑ i : Lattice.Site N, (p : HilbertConfiguration N) i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [inverseMassMomentum_apply]
          field_simp [ne_of_gt (m.mass_pos i)]
    _ = 0 := hp

@[simp] theorem reducedVelocity_coe {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : ReducedMomentumSpace N) :
    (reducedVelocity m p : HilbertConfiguration N) =
      inverseMassMomentum m (p : HilbertConfiguration N) := by
  rfl

/-- The reduced inverse-mass velocity as a linear map. -/
def reducedVelocityLinearMap {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    ReducedMomentumSpace N →ₗ[Real] ReducedPositionSpace m where
  toFun := reducedVelocity m
  map_add' p r := by
    apply Subtype.ext
    ext i
    simp only [reducedVelocity_coe, inverseMassMomentum_apply, Submodule.coe_add,
      PiLp.add_apply]
    ring
  map_smul' c p := by
    apply Subtype.ext
    ext i
    simp only [reducedVelocity_coe, inverseMassMomentum_apply, Submodule.coe_smul,
      PiLp.smul_apply, RingHom.id_apply]
    ring

/-- Continuous-linear realization of the reduced inverse-mass velocity. -/
def reducedVelocityCLM {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    ReducedMomentumSpace N →L[Real] ReducedPositionSpace m :=
  LinearMap.toContinuousLinearMap (reducedVelocityLinearMap m)

/-- The reduced polynomial potential gradient is continuously differentiable. -/
theorem reducedPotentialGradient_contDiff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real) :
    ContDiff Real 1 (reducedPotentialGradient m kappa beta g) := by
  unfold reducedPotentialGradient
  apply ContDiff.sum
  intro i _
  apply ContDiff.smul_const
  unfold potentialDerivative
  fun_prop

/-- The explicit translation-reduced Hamilton vector field on `(q,p)`. -/
def reducedVectorField {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real) :
    ReducedPhaseSpace m → ReducedPhaseSpace m :=
  fun z ↦ (reducedVelocity m z.2, -reducedPotentialGradient m kappa beta g z.1)

/-- The concrete reduced Hamilton vector field is `C¹`. -/
theorem reducedVectorField_contDiff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real) :
    ContDiff Real 1 (reducedVectorField m kappa beta g) := by
  have hvelocity : ContDiff Real 1
      (fun z : ReducedPhaseSpace m ↦ reducedVelocity m z.2) :=
    (reducedVelocityCLM m).contDiff.comp (by fun_prop)
  have hgradient : ContDiff Real 1
      (fun z : ReducedPhaseSpace m ↦
        reducedPotentialGradient m kappa beta g z.1) :=
    (reducedPotentialGradient_contDiff m kappa beta g).comp (by fun_prop)
  exact hvelocity.prodMk hgradient.neg

/-- Consequently the concrete reduced vector field is locally Lipschitz. -/
theorem reducedVectorField_locallyLipschitz {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real) :
    LocallyLipschitz (reducedVectorField m kappa beta g) :=
  (reducedVectorField_contDiff m kappa beta g).locallyLipschitz

/-- Stabilized Hamiltonian restricted to the translation-reduced phase space. -/
def reducedHamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (z : ReducedPhaseSpace m) : Real :=
  CoerciveLatticeEnergy.hamiltonian m kappa beta g
    (asConfiguration (z.2 : HilbertConfiguration N))
    (asConfiguration (z.1 : HilbertConfiguration N))

/-- The restricted Hamiltonian has derivative zero at every point of a
reduced integral curve. -/
theorem reducedHamiltonian_hasDerivWithinAt_zero {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {z : Real → ReducedPhaseSpace m} {s : Set Real} {t : Real}
    (hz : HasDerivWithinAt z (reducedVectorField m kappa beta g (z t)) s t) :
    HasDerivWithinAt (fun u ↦ reducedHamiltonian m kappa beta g (z u)) 0 s t := by
  have hqSub : HasDerivWithinAt (fun u ↦ (z u).1)
      (reducedVelocity m (z t).2) s t := by
    simpa [reducedVectorField] using
      hz.hasFDerivWithinAt.fst.hasDerivWithinAt
  have hpSub : HasDerivWithinAt (fun u ↦ (z u).2)
      (-reducedPotentialGradient m kappa beta g (z t).1) s t := by
    simpa [reducedVectorField] using
      hz.hasFDerivWithinAt.snd.hasDerivWithinAt
  have hq :=
    (ReducedPositionSpace m).subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hqSub
  have hp :=
    (ReducedMomentumSpace N).subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hpSub
  have hkin :=
    (hasGradientAt_kineticEnergy m ((z t).2 : HilbertConfiguration N)).hasFDerivAt
      |>.comp_hasDerivWithinAt t hp
  have hpot :=
    (hasGradientAt_potentialEnergy kappa beta g
      ((z t).1 : HilbertConfiguration N)).hasFDerivAt
      |>.comp_hasDerivWithinAt t hq
  have hsum := hkin.add hpot
  simpa [reducedHamiltonian, CoerciveLatticeEnergy.hamiltonian, Function.comp_def,
    InnerProductSpace.toDual_apply_apply, real_inner_comm] using! hsum

/-- Energy agrees at any two times in an interval carrying the reduced ODE. -/
theorem reducedHamiltonian_eq_of_integralCurveOn {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {z : Real → ReducedPhaseSpace m} {s : Set Real}
    (hs : Convex Real s)
    (hz : IsIntegralCurveOn z (fun _ ↦ reducedVectorField m kappa beta g) s)
    {u v : Real} (hu : u ∈ s) (hv : v ∈ s) :
    reducedHamiltonian m kappa beta g (z u) =
      reducedHamiltonian m kappa beta g (z v) := by
  let energy : Real → Real := fun t ↦ reducedHamiltonian m kappa beta g (z t)
  have hzero : ∀ t ∈ s, HasDerivWithinAt energy 0 s t := by
    intro t ht
    exact reducedHamiltonian_hasDerivWithinAt_zero m kappa beta g (hz t ht)
  have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hzero (fun _ _ ↦ by simp) hu hv
  have hrev : energy v = energy u := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  exact hrev.symm


/-- Forward differences as a linear map between Euclidean configurations. -/
def hilbertForwardDifferenceLinearMap (N : Nat) [NeZero N] :
    HilbertConfiguration N →ₗ[Real] HilbertConfiguration N where
  toFun q := WithLp.toLp 2 fun i ↦
    Lattice.forwardDifference (asConfiguration q) i
  map_add' q r := by
    ext i
    simp [Lattice.forwardDifference, asConfiguration]
    ring
  map_smul' c q := by
    ext i
    simp [Lattice.forwardDifference, asConfiguration, mul_sub]

@[simp] theorem hilbertForwardDifferenceLinearMap_apply
    {N : Nat} [NeZero N] (q : HilbertConfiguration N) (i : Lattice.Site N) :
    hilbertForwardDifferenceLinearMap N q i =
      Lattice.forwardDifference (asConfiguration q) i := by
  rfl

/-- The Euclidean adapter is exactly the existing translation-reduced
forward-difference linear map after forgetting the Hilbert wrapper. -/
theorem asConfiguration_hilbertForwardDifferenceLinearMap
    {N : Nat} [NeZero N] (q : HilbertConfiguration N) :
    asConfiguration (hilbertForwardDifferenceLinearMap N q) =
      forwardDifferenceLinearMap N (asConfiguration q) := by
  ext i
  rw [forwardDifferenceLinearMap_apply]
  rfl


/-- Forward difference restricted to the mass-weighted translation gauge. -/
def massWeightedReducedDifferenceLinearMap {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    ReducedPositionSpace m →ₗ[Real] HilbertConfiguration N :=
  (hilbertForwardDifferenceLinearMap N).comp (ReducedPositionSpace m).subtype

/-- The mass-weighted gauge meets the translation kernel only at zero. -/
theorem massWeightedReducedDifferenceLinearMap_injective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Function.Injective (massWeightedReducedDifferenceLinearMap m) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro q hq
  rw [LinearMap.mem_ker] at hq
  have hdifference :
      Lattice.forwardDifference
        (asConfiguration (q : HilbertConfiguration N)) = 0 := by
    funext i
    have hi := congrArg (fun v : HilbertConfiguration N ↦ v i) hq
    simpa [massWeightedReducedDifferenceLinearMap] using hi
  obtain ⟨c, hc⟩ :
      ∃ c : Real, asConfiguration (q : HilbertConfiguration N) = fun _ ↦ c :=
    (ReducedHarmonicSpectrum.forwardDifference_eq_zero_iff_constant
      (asConfiguration (q : HilbertConfiguration N))).mp hdifference
  have hmassSumPos : 0 < ∑ i : Lattice.Site N, m.mass i :=
    Finset.sum_pos (fun i _ ↦ m.mass_pos i) Finset.univ_nonempty
  have hweighted :
      ∑ i : Lattice.Site N, m.mass i * (q : HilbertConfiguration N) i = 0 :=
    (mem_reducedPositionSpace_iff m _).1 q.property
  have hcProduct : (∑ i : Lattice.Site N, m.mass i) * c = 0 := by
    rw [Finset.sum_mul]
    calc
      (∑ i : Lattice.Site N, m.mass i * c) =
          ∑ i : Lattice.Site N, m.mass i * (q : HilbertConfiguration N) i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show (q : HilbertConfiguration N) i = c by
              exact congrFun hc i]
      _ = 0 := hweighted
  have hcZero : c = 0 :=
    (mul_eq_zero.mp hcProduct).resolve_left (ne_of_gt hmassSumPos)
  apply Subtype.ext
  ext i
  exact (congrFun hc i).trans hcZero

/-- Finite-dimensional Poincare inequality on the mass-weighted gauge. -/
theorem exists_massWeightedReduced_poincareConstant
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    ∃ C : Real, 0 < C ∧ ∀ q : ReducedPositionSpace m,
      ‖q‖ ≤ C * ‖massWeightedReducedDifferenceLinearMap m q‖ := by
  obtain ⟨K, hK, hAnti⟩ :=
    (LinearMap.injective_iff_antilipschitz
      (massWeightedReducedDifferenceLinearMap m)).mp
      (massWeightedReducedDifferenceLinearMap_injective m)
  refine ⟨K, by exact_mod_cast hK, fun q ↦ ?_⟩
  exact ZeroHomClass.bound_of_antilipschitz
    (massWeightedReducedDifferenceLinearMap m) hAnti q

/-- Euclidean squared norm of the difference vector is the bond square sum. -/
theorem massWeightedReducedDifference_norm_sq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : ReducedPositionSpace m) :
    ‖massWeightedReducedDifferenceLinearMap m q‖ ^ 2 =
      ∑ i : Lattice.Site N,
        Lattice.forwardDifference
          (asConfiguration (q : HilbertConfiguration N)) i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

private theorem norm_le_sq_add_one
    {E : Type*} [SeminormedAddGroup E] (x : E) :
    ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by
  nlinarith [sq_nonneg (‖x‖ - (1 / 2 : Real))]


/-- A coercive energy sublevel is norm-bounded on the reduced phase space. -/
theorem exists_reducedPhaseSpace_norm_bound_of_energy_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g H : Real) :
    ∃ R : Real, ∀ z : ReducedPhaseSpace m,
      reducedHamiltonian m kappa beta g z ≤ H → ‖z‖ ≤ R := by
  obtain ⟨C, hC, hPoincare⟩ :=
    exists_massWeightedReduced_poincareConstant m
  let differenceBound : Real :=
    H / CoerciveCubicPotential.coercivityConstant kappa beta + 1
  let momentumBound : Real :=
    (∑ i : Lattice.Site N, 2 * m.mass i * H) + 1
  refine ⟨max (C * differenceBound) momentumBound, fun z henergy ↦ ?_⟩
  have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
    CoerciveCubicPotential.coercivityConstant_pos hbeta
  have hdifferenceEnergy :
      (∑ i : Lattice.Site N,
        Lattice.forwardDifference
          (asConfiguration (z.1 : HilbertConfiguration N)) i ^ 2) ≤
        reducedHamiltonian m kappa beta g z /
          CoerciveCubicPotential.coercivityConstant kappa beta := by
    exact CoerciveLatticeEnergy.sum_sq_forwardDifference_le_energy_div
      m hbeta g (asConfiguration (z.2 : HilbertConfiguration N))
        (asConfiguration (z.1 : HilbertConfiguration N))
  have hdifferenceH :
      (∑ i : Lattice.Site N,
        Lattice.forwardDifference
          (asConfiguration (z.1 : HilbertConfiguration N)) i ^ 2) ≤
        H / CoerciveCubicPotential.coercivityConstant kappa beta := by
    exact hdifferenceEnergy.trans
      (div_le_div_of_nonneg_right henergy hc.le)
  have hdifferenceSq :
      ‖massWeightedReducedDifferenceLinearMap m z.1‖ ^ 2 ≤
        H / CoerciveCubicPotential.coercivityConstant kappa beta := by
    rw [massWeightedReducedDifference_norm_sq]
    exact hdifferenceH
  have hdifferenceNorm :
      ‖massWeightedReducedDifferenceLinearMap m z.1‖ ≤ differenceBound := by
    unfold differenceBound
    exact (norm_le_sq_add_one
      (massWeightedReducedDifferenceLinearMap m z.1)).trans
      (by linarith)
  have hq : ‖z.1‖ ≤ C * differenceBound :=
    (hPoincare z.1).trans
      (mul_le_mul_of_nonneg_left hdifferenceNorm hC.le)
  have hpCoordinate (i : Lattice.Site N) :
      (z.2 : HilbertConfiguration N) i ^ 2 ≤ 2 * m.mass i * H := by
    have hpoint :
        (z.2 : HilbertConfiguration N) i ^ 2 ≤
          2 * m.mass i * reducedHamiltonian m kappa beta g z := by
      exact CoerciveLatticeEnergy.momentum_sq_le_mass_mul_energy
        m hbeta g (asConfiguration (z.2 : HilbertConfiguration N))
          (asConfiguration (z.1 : HilbertConfiguration N)) i
    exact hpoint.trans
      (mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (by norm_num) (m.mass_pos i).le))
  have hpSq :
      ‖(z.2 : HilbertConfiguration N)‖ ^ 2 ≤
        ∑ i : Lattice.Site N, 2 * m.mass i * H := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum fun i _ ↦ hpCoordinate i
  have hpAmbient :
      ‖(z.2 : HilbertConfiguration N)‖ ≤ momentumBound := by
    unfold momentumBound
    exact (norm_le_sq_add_one (z.2 : HilbertConfiguration N)).trans
      (by linarith)
  have hp : ‖z.2‖ ≤ momentumBound := by
    exact hpAmbient
  rw [Prod.norm_def]
  exact max_le_max hq hp

/-- Energy conservation plus coercivity makes a reduced trajectory bounded on
every finite half-open interval. -/
theorem bounded_image_of_reduced_integralCurveOn
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    {z : Real → ReducedPhaseSpace m} {t₀ b : Real} (ht : t₀ < b)
    (hz : IsIntegralCurveOn z
      (fun _ ↦ reducedVectorField m kappa beta g) (Ico t₀ b)) :
    Bornology.IsBounded (z '' Ico t₀ b) := by
  let initialEnergy := reducedHamiltonian m kappa beta g (z t₀)
  obtain ⟨R, hR⟩ :=
    exists_reducedPhaseSpace_norm_bound_of_energy_le m hbeta g initialEnergy
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R, ?_⟩
  rintro x ⟨t, htInterval, rfl⟩
  apply hR
  have henergy :
      reducedHamiltonian m kappa beta g (z t) = initialEnergy := by
    exact reducedHamiltonian_eq_of_integralCurveOn m kappa beta g
      (convex_Ico t₀ b) hz htInterval ⟨le_rfl, ht⟩
  exact henergy.le

/-- Every finite-endpoint reduced solution has a strict forward extension. -/
theorem exists_strictForwardExtension_of_reduced_integralCurveOn
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    {z : Real → ReducedPhaseSpace m} {t₀ b : Real} (ht : t₀ < b)
    (hz : IsIntegralCurveOn z
      (fun _ ↦ reducedVectorField m kappa beta g) (Ico t₀ b)) :
    ∃ (b' : Real) (delta : Real → ReducedPhaseSpace m),
      IsStrictForwardExtension (reducedVectorField m kappa beta g)
        z delta t₀ b b' := by
  exact exists_strictForwardExtension_of_bounded ht
    (reducedVectorField_contDiff m kappa beta g) hz
    (bounded_image_of_reduced_integralCurveOn m hbeta g ht hz)

/-- A finite-energy reduced Hamiltonian trajectory cannot be forward maximal
at a finite endpoint. -/
theorem not_isForwardMaximalAt_reduced_integralCurveOn
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    {z : Real → ReducedPhaseSpace m} {t₀ b : Real} (ht : t₀ < b)
    (hz : IsIntegralCurveOn z
      (fun _ ↦ reducedVectorField m kappa beta g) (Ico t₀ b)) :
    ¬ IsForwardMaximalAt (reducedVectorField m kappa beta g) z t₀ b := by
  exact not_isForwardMaximalAt_of_bounded ht
    (reducedVectorField_contDiff m kappa beta g) hz
    (bounded_image_of_reduced_integralCurveOn m hbeta g ht hz)

end

end ArchonPhysics.CoerciveHamiltonianContinuation
