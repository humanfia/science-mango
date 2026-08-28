import ArchonPhysics.CleanCycleAcousticCountEnvelope
import ArchonPhysics.RandomMassSiteCoefficientDynamics
import Mathlib.Analysis.Fourier.ZMod

/-!
# Equal-mass periodic alpha-FPUT in the complex Fourier basis

This module fixes the canonical additive-character Fourier labels of
`Lattice.Site N = ZMod N`.  It proves the exact three-bond character tensor,
including its lattice-momentum selector, and then projects the existing
Physlib site Hamilton equations onto those same Fourier coordinates.

The basis is the explicit clean-cycle character basis, not an arbitrary real
eigenbasis.  All statements are finite-volume identities.  No resonant-shell,
random-phase, or kinetic-limit assertion is made.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian

open scoped BigOperators ComplexConjugate

open ArchonPhysics
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.Lattice
open ArchonPhysics.RandomMassSiteCoefficientDynamics
open Time

noncomputable section

/-! ## Canonical character waves and bond symbols -/

/-- The canonical positive-exponent Fourier character at lattice momentum
`k`. -/
def fourierWave (N : Nat) [NeZero N] (k x : Site N) : Complex :=
  cleanCycleFourierBasis N k x

/-- Forward-bond multiplier `exp(2 pi i k/N) - 1`. -/
def bondFourierSymbol (N : Nat) [NeZero N] (k : Site N) : Complex :=
  fourierWave N k 1 - 1

/-- Complex forward difference on periodic site functions. -/
def complexForwardDifference {N : Nat} (u : Site N → Complex) :
    Site N → Complex :=
  fun x ↦ u (x + 1) - u x

/-- Complex incoming-minus-outgoing difference. -/
def complexBackwardDifference {N : Nat} (u : Site N → Complex) :
    Site N → Complex :=
  fun x ↦ u (x - 1) - u x

/-- Multiplier for the outgoing-minus-incoming bond divergence. -/
def outgoingFourierSymbol (N : Nat) [NeZero N] (k : Site N) : Complex :=
  1 - fourierWave N k (-1)

/-- Outgoing-minus-incoming divergence on a periodic site field. -/
def complexOutgoingMinusIncoming {N : Nat} (u : Site N → Complex) :
    Site N → Complex :=
  fun x ↦ u x - u (x - 1)

@[simp] theorem fourierWave_zero_momentum
    (N : Nat) [NeZero N] (x : Site N) :
    fourierWave N 0 x = 1 := by
  simp only [fourierWave, cleanCycleFourierBasis_apply]
  rw [(AddChar.zmodAddEquiv (n := N)).map_zero]
  exact AddChar.zero_apply x

@[simp] theorem fourierWave_at_zero
    (N : Nat) [NeZero N] (k : Site N) :
    fourierWave N k 0 = 1 := by
  simp [fourierWave]

theorem fourierWave_add
    (N : Nat) [NeZero N] (k l x : Site N) :
    fourierWave N (k + l) x = fourierWave N k x * fourierWave N l x := by
  simp only [fourierWave, cleanCycleFourierBasis_apply]
  rw [(AddChar.zmodAddEquiv (n := N)).map_add]
  rfl

theorem fourierWave_site_add
    (N : Nat) [NeZero N] (k x y : Site N) :
    fourierWave N k (x + y) = fourierWave N k x * fourierWave N k y := by
  simp only [fourierWave, cleanCycleFourierBasis_apply]
  exact AddChar.map_add_eq_mul _ _ _

@[simp] theorem bondFourierSymbol_zero (N : Nat) [NeZero N] :
    bondFourierSymbol N 0 = 0 := by
  simp [bondFourierSymbol]

@[simp] theorem outgoingFourierSymbol_zero (N : Nat) [NeZero N] :
    outgoingFourierSymbol N 0 = 0 := by
  simp [outgoingFourierSymbol]

theorem complexForwardDifference_fourierWave
    (N : Nat) [NeZero N] (k x : Site N) :
    complexForwardDifference (fourierWave N k) x =
      bondFourierSymbol N k * fourierWave N k x := by
  unfold complexForwardDifference bondFourierSymbol
  rw [fourierWave_site_add]
  ring

theorem complexBackwardDifference_fourierWave
    (N : Nat) [NeZero N] (k x : Site N) :
    complexBackwardDifference (fourierWave N k) x =
      bondFourierSymbol N (-k) * fourierWave N k x := by
  unfold complexBackwardDifference bondFourierSymbol
  rw [show x - 1 = x + (-1 : Site N) by ring,
    fourierWave_site_add]
  have hneg : fourierWave N k (-1) = fourierWave N (-k) 1 := by
    simp only [fourierWave, cleanCycleFourierBasis_apply]
    rw [← AddChar.neg_apply]
    rw [← (AddChar.zmodAddEquiv (n := N)).map_neg k]
  rw [hneg]
  ring

theorem complexOutgoingMinusIncoming_fourierWave
    (N : Nat) [NeZero N] (k x : Site N) :
    complexOutgoingMinusIncoming (fourierWave N k) x =
      outgoingFourierSymbol N k * fourierWave N k x := by
  unfold complexOutgoingMinusIncoming outgoingFourierSymbol
  rw [show x - 1 = x + (-1 : Site N) by ring,
    fourierWave_site_add]
  ring

/-- Exact finite character sum on `ZMod N`. -/
theorem sum_fourierWave_eq_ite
    (N : Nat) [NeZero N] (k : Site N) :
    (∑ x : Site N, fourierWave N k x) =
      if k = 0 then (N : Complex) else 0 := by
  simp only [fourierWave, cleanCycleFourierBasis_apply]
  rw [AddChar.sum_eq_ite]
  simp only [(AddChar.zmodAddEquiv (n := N)).map_eq_zero_iff, ZMod.card]

theorem fourierWave_neg_momentum
    (N : Nat) [NeZero N] (k x : Site N) :
    fourierWave N (-k) x = conj (fourierWave N k x) := by
  simp only [fourierWave, cleanCycleFourierBasis_apply]
  calc
    ((AddChar.zmodAddEquiv (n := N)) (-k)) x =
        (-((AddChar.zmodAddEquiv (n := N)) k)) x := by
          rw [(AddChar.zmodAddEquiv (n := N)).map_neg]
    _ = ((AddChar.zmodAddEquiv (n := N)) k) (-x) := rfl
    _ = conj (((AddChar.zmodAddEquiv (n := N)) k) x) :=
      AddChar.map_neg_eq_conj _ _

/-- Orthogonality of the unnormalized character waves. -/
theorem sum_conj_fourierWave_mul_eq_ite
    (N : Nat) [NeZero N] (k l : Site N) :
    (∑ x : Site N, conj (fourierWave N k x) * fourierWave N l x) =
      if k = l then (N : Complex) else 0 := by
  simp_rw [← fourierWave_neg_momentum, ← fourierWave_add]
  rw [sum_fourierWave_eq_ite]
  have hzero : -k + l = 0 ↔ k = l := by
    exact neg_add_eq_zero
  rw [if_congr hzero rfl rfl]

/-- Average-normalized complex Fourier coefficient on the finite cycle. -/
def cycleFourierCoefficient
    {N : Nat} [NeZero N] (u : Site N → Complex) (k : Site N) : Complex :=
  (N : Complex)⁻¹ *
    ∑ x : Site N, conj (fourierWave N k x) * u x

@[simp] theorem cycleFourierCoefficient_fourierWave
    (N : Nat) [NeZero N] (k l : Site N) :
    cycleFourierCoefficient (fourierWave N l) k = if k = l then 1 else 0 := by
  unfold cycleFourierCoefficient
  rw [sum_conj_fourierWave_mul_eq_ite]
  split_ifs
  · rw [inv_mul_cancel₀]
    exact_mod_cast NeZero.ne N
  · simp

theorem cycleFourierCoefficient_add
    {N : Nat} [NeZero N] (u v : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (u + v) k =
      cycleFourierCoefficient u k + cycleFourierCoefficient v k := by
  unfold cycleFourierCoefficient
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cycleFourierCoefficient_smul
    {N : Nat} [NeZero N] (c : Complex) (u : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (c • u) k = c * cycleFourierCoefficient u k := by
  unfold cycleFourierCoefficient
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (N : Complex)⁻¹ *
        ∑ x, conj (fourierWave N k x) * (c * u x) =
        (N : Complex)⁻¹ *
          ∑ x, c * (conj (fourierWave N k x) * u x) := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _hx
            ring
    _ = (N : Complex)⁻¹ *
        (c * ∑ x, conj (fourierWave N k x) * u x) := by
          apply congrArg ((N : Complex)⁻¹ * ·)
          exact (Finset.mul_sum _ _ c).symm
    _ = c * ((N : Complex)⁻¹ *
        ∑ x, conj (fourierWave N k x) * u x) := by ring

theorem cycleFourierCoefficient_sum
    {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (u : ι → Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (∑ i, u i) k =
      ∑ i, cycleFourierCoefficient (u i) k := by
  classical
  unfold cycleFourierCoefficient
  simp_rw [Fintype.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cycleFourierCoefficient_eq_repr
    {N : Nat} [NeZero N] (u : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient u k =
      (cleanCycleFourierBasis N).repr u k := by
  rw [← (cleanCycleFourierBasis N).sum_repr u,
    cycleFourierCoefficient_sum]
  simp only [cycleFourierCoefficient_smul]
  change (∑ x : Site N, ((cleanCycleFourierBasis N).repr u) x *
    cycleFourierCoefficient (fourierWave N x) k) = _
  simp

/-- Exact reconstruction from the average-normalized Fourier coefficients. -/
theorem cycleFourier_reconstruct
    {N : Nat} [NeZero N] (u : Site N → Complex) (x : Site N) :
    (∑ k : Site N,
        cycleFourierCoefficient u k * fourierWave N k x) = u x := by
  simp_rw [cycleFourierCoefficient_eq_repr]
  have h := congrFun ((cleanCycleFourierBasis N).sum_repr u) x
  simpa only [fourierWave, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    using h

theorem cycleFourier_expansion
    {N : Nat} [NeZero N] (u : Site N → Complex) :
    u = ∑ k : Site N,
      cycleFourierCoefficient u k • fourierWave N k := by
  funext x
  simpa only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    using (cycleFourier_reconstruct u x).symm

/-- The forward bond difference is diagonal in the canonical character
basis. -/
theorem cycleFourierCoefficient_forwardDifference
    {N : Nat} [NeZero N] (u : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (complexForwardDifference u) k =
      bondFourierSymbol N k * cycleFourierCoefficient u k := by
  have hdiff :
      complexForwardDifference
          (∑ l : Site N,
            cycleFourierCoefficient u l • fourierWave N l) =
        ∑ l : Site N,
          (cycleFourierCoefficient u l * bondFourierSymbol N l) •
            fourierWave N l := by
    funext x
    unfold complexForwardDifference
    simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    calc
      cycleFourierCoefficient u l * fourierWave N l (x + 1) -
          cycleFourierCoefficient u l * fourierWave N l x =
          cycleFourierCoefficient u l *
            (fourierWave N l (x + 1) - fourierWave N l x) := by ring
      _ = cycleFourierCoefficient u l *
          (bondFourierSymbol N l * fourierWave N l x) := by
            rw [show fourierWave N l (x + 1) - fourierWave N l x =
                bondFourierSymbol N l * fourierWave N l x from
              complexForwardDifference_fourierWave N l x]
      _ = cycleFourierCoefficient u l * bondFourierSymbol N l *
          fourierWave N l x := by ring
  rw [show complexForwardDifference u =
      complexForwardDifference
        (∑ l : Site N,
          cycleFourierCoefficient u l • fourierWave N l) by
        rw [← cycleFourier_expansion u],
    hdiff, cycleFourierCoefficient_sum]
  simp only [cycleFourierCoefficient_smul,
    cycleFourierCoefficient_fourierWave]
  simp
  ring

theorem cycleFourierCoefficient_outgoingMinusIncoming
    {N : Nat} [NeZero N] (u : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (complexOutgoingMinusIncoming u) k =
      outgoingFourierSymbol N k * cycleFourierCoefficient u k := by
  have hdiv :
      complexOutgoingMinusIncoming
          (∑ l : Site N,
            cycleFourierCoefficient u l • fourierWave N l) =
        ∑ l : Site N,
          (cycleFourierCoefficient u l * outgoingFourierSymbol N l) •
            fourierWave N l := by
    funext x
    unfold complexOutgoingMinusIncoming
    simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    calc
      cycleFourierCoefficient u l * fourierWave N l x -
          cycleFourierCoefficient u l * fourierWave N l (x - 1) =
          cycleFourierCoefficient u l *
            (fourierWave N l x - fourierWave N l (x - 1)) := by ring
      _ = cycleFourierCoefficient u l *
          (outgoingFourierSymbol N l * fourierWave N l x) := by
            rw [show fourierWave N l x - fourierWave N l (x - 1) =
                outgoingFourierSymbol N l * fourierWave N l x from
              complexOutgoingMinusIncoming_fourierWave N l x]
      _ = cycleFourierCoefficient u l * outgoingFourierSymbol N l *
          fourierWave N l x := by ring
  rw [show complexOutgoingMinusIncoming u =
      complexOutgoingMinusIncoming
        (∑ l : Site N,
          cycleFourierCoefficient u l • fourierWave N l) by
        rw [← cycleFourier_expansion u],
    hdiv, cycleFourierCoefficient_sum]
  simp only [cycleFourierCoefficient_smul,
    cycleFourierCoefficient_fourierWave]
  simp
  ring

/-- Harmonic bond multiplier, with the exact sign used by Hamilton's force
equation. -/
theorem outgoing_mul_bond_eq_neg_modeEnergy
    (N : Nat) [NeZero N] (k : Site N) :
    outgoingFourierSymbol N k * bondFourierSymbol N k =
      -(cleanCycleModeEnergy N k : Complex) := by
  have hunit : fourierWave N k (-1) * fourierWave N k 1 = 1 := by
    rw [← fourierWave_site_add]
    simp
  have henergy : (cleanCycleModeEnergy N k : Complex) =
      2 - fourierWave N k (-1) - fourierWave N k 1 := by
    rw [cleanCycleModeEnergy_fourier]
    simp only [fourierWave]
    norm_num
  rw [henergy]
  simp only [outgoingFourierSymbol, bondFourierSymbol]
  calc
    (1 - fourierWave N k (-1)) * (fourierWave N k 1 - 1) =
        fourierWave N k 1 - 1 -
          fourierWave N k (-1) * fourierWave N k 1 +
          fourierWave N k (-1) := by ring
    _ = fourierWave N k 1 - 1 - 1 + fourierWave N k (-1) := by
      rw [hunit]
    _ = -(2 - fourierWave N k (-1) - fourierWave N k 1) := by ring

/-- Product-convolution identity for the average-normalized finite Fourier
transform. -/
theorem cycleFourierCoefficient_mul
    {N : Nat} [NeZero N] (u v : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient (u * v) k =
      ∑ l : Site N,
        cycleFourierCoefficient u l * cycleFourierCoefficient v (k - l) := by
  rw [cycleFourier_expansion u, cycleFourier_expansion v]
  have hproduct :
      (∑ l : Site N,
          cycleFourierCoefficient u l • fourierWave N l) *
        (∑ m : Site N,
          cycleFourierCoefficient v m • fourierWave N m) =
      ∑ l : Site N, ∑ m : Site N,
        (cycleFourierCoefficient u l * cycleFourierCoefficient v m) •
          fourierWave N (l + m) := by
    funext x
    simp only [Pi.mul_apply, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    rw [fourierWave_add]
    ring
  rw [hproduct, cycleFourierCoefficient_sum]
  simp_rw [cycleFourierCoefficient_sum, cycleFourierCoefficient_smul,
    cycleFourierCoefficient_fourierWave]
  simp only [mul_ite, mul_one, mul_zero]
  have hselector (l m : Site N) : (k = l + m) = (m = k - l) := by
    apply propext
    constructor <;> intro h
    · rw [h]
      ring
    · rw [h]
      ring
  simp_rw [hselector]
  simp

/-- Fourier coefficient of the squared bond strain. -/
theorem cycleFourierCoefficient_forwardDifference_sq
    {N : Nat} [NeZero N] (u : Site N → Complex) (k : Site N) :
    cycleFourierCoefficient
        (fun x ↦ (complexForwardDifference u x) ^ 2) k =
      ∑ l : Site N,
        bondFourierSymbol N l * bondFourierSymbol N (k - l) *
          cycleFourierCoefficient u l *
          cycleFourierCoefficient u (k - l) := by
  rw [show (fun x ↦ (complexForwardDifference u x) ^ 2) =
      complexForwardDifference u * complexForwardDifference u by
        funext x
        simp only [Pi.mul_apply, pow_two]]
  rw [cycleFourierCoefficient_mul]
  simp_rw [cycleFourierCoefficient_forwardDifference]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

/-! ## Three-bond tensor and exact momentum support -/

/-- Unnormalized cubic bond tensor in the canonical complex Fourier basis. -/
def bondDifferenceCubicTensor
    (N : Nat) [NeZero N] (k₀ k₁ k₂ : Site N) : Complex :=
  ∑ x : Site N,
    complexForwardDifference (fourierWave N k₀) x *
      complexForwardDifference (fourierWave N k₁) x *
      complexForwardDifference (fourierWave N k₂) x

/-- The three-bond tensor is a product of bond symbols times the exact
`ZMod N` momentum selector. -/
theorem bondDifferenceCubicTensor_eq_ite
    (N : Nat) [NeZero N] (k₀ k₁ k₂ : Site N) :
    bondDifferenceCubicTensor N k₀ k₁ k₂ =
      if k₀ + k₁ + k₂ = 0 then
        (N : Complex) * bondFourierSymbol N k₀ *
          bondFourierSymbol N k₁ * bondFourierSymbol N k₂
      else 0 := by
  unfold bondDifferenceCubicTensor
  simp_rw [complexForwardDifference_fourierWave]
  rw [show (∑ x : Site N,
      bondFourierSymbol N k₀ * fourierWave N k₀ x *
        (bondFourierSymbol N k₁ * fourierWave N k₁ x) *
        (bondFourierSymbol N k₂ * fourierWave N k₂ x)) =
      bondFourierSymbol N k₀ * bondFourierSymbol N k₁ *
        bondFourierSymbol N k₂ *
          ∑ x : Site N, fourierWave N (k₀ + k₁ + k₂) x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [fourierWave_add, fourierWave_add]
    ring]
  rw [sum_fourierWave_eq_ite]
  split_ifs <;> ring

theorem bondDifferenceCubicTensor_eq_zero_of_momentum_ne
    (N : Nat) [NeZero N] {k₀ k₁ k₂ : Site N}
    (hmomentum : k₀ + k₁ + k₂ ≠ 0) :
    bondDifferenceCubicTensor N k₀ k₁ k₂ = 0 := by
  rw [bondDifferenceCubicTensor_eq_ite, if_neg hmomentum]

theorem bondDifferenceCubicTensor_eq_zero_of_first_zero
    (N : Nat) [NeZero N] (k₁ k₂ : Site N) :
    bondDifferenceCubicTensor N 0 k₁ k₂ = 0 := by
  rw [bondDifferenceCubicTensor_eq_ite]
  split_ifs <;> simp

theorem bondDifferenceCubicTensor_eq_zero_of_second_zero
    (N : Nat) [NeZero N] (k₀ k₂ : Site N) :
    bondDifferenceCubicTensor N k₀ 0 k₂ = 0 := by
  rw [bondDifferenceCubicTensor_eq_ite]
  split_ifs <;> simp

theorem bondDifferenceCubicTensor_eq_zero_of_third_zero
    (N : Nat) [NeZero N] (k₀ k₁ : Site N) :
    bondDifferenceCubicTensor N k₀ k₁ 0 = 0 := by
  rw [bondDifferenceCubicTensor_eq_ite]
  split_ifs <;> simp

/-! ## Pure-alpha Hamilton equations and complex Fourier projection -/

/-- Equal unit masses on the finite periodic chain. -/
def unitMassConfig (N : Nat) : PositiveMassConfig N where
  mass := fun _ ↦ 1
  mass_pos := fun _ ↦ by norm_num

@[simp] theorem unitMassConfig_mass {N : Nat} (i : Site N) :
    (unitMassConfig N).mass i = 1 := rfl

@[simp] theorem inverseMassMomentum_unitMass
    {N : Nat} [NeZero N] (p : HilbertConfiguration N) :
    inverseMassMomentum (unitMassConfig N) p = p := by
  ext i
  simp [inverseMassMomentum_apply]

@[simp] theorem potentialDerivative_pureAlpha (alpha x : Real) :
    potentialDerivative 1 0 alpha x = x + alpha * x ^ 2 := by
  simp [potentialDerivative]

/-- Site form of the pure-alpha force (outgoing bond force minus incoming
bond force). -/
theorem neg_potentialGradient_pureAlpha_apply
    {N : Nat} [NeZero N] (alpha : Real)
    (q : HilbertConfiguration N) (i : Site N) :
    (-potentialGradient 1 0 alpha q) i =
      (Lattice.forwardDifference (asConfiguration q) i +
          alpha * Lattice.forwardDifference (asConfiguration q) i ^ 2) -
        (Lattice.forwardDifference (asConfiguration q) (i - 1) +
          alpha * Lattice.forwardDifference (asConfiguration q) (i - 1) ^ 2) := by
  rw [PiLp.neg_apply,
    potentialGradient_apply_eq_incoming_sub_outgoing]
  simp only [potentialDerivative_pureAlpha]
  ring

/-- The existing Physlib Hamilton predicate, specialized exactly to equal
unit masses and the pure-alpha bond force. -/
theorem pureAlpha_satisfiesHamiltonEquations_iff_site
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) :
    SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q ↔
      (∀ t, ∂ₜ q t = p t) ∧
      (∀ t i,
        (∂ₜ p t) i =
          (Lattice.forwardDifference (asConfiguration (q t)) i +
              alpha * Lattice.forwardDifference (asConfiguration (q t)) i ^ 2) -
            (Lattice.forwardDifference (asConfiguration (q t)) (i - 1) +
              alpha * Lattice.forwardDifference
                (asConfiguration (q t)) (i - 1) ^ 2)) := by
  rw [satisfiesHamiltonEquations_iff_explicit]
  constructor
  · rintro ⟨hq, hp⟩
    exact ⟨fun t ↦ by simpa using hq t,
      fun t i ↦ by
        rw [hp t]
        exact neg_potentialGradient_pureAlpha_apply alpha (q t) i⟩
  · rintro ⟨hq, hp⟩
    constructor
    · intro t
      simpa using hq t
    · intro t
      ext i
      rw [hp t i]
      exact (neg_potentialGradient_pureAlpha_apply alpha (q t) i).symm

/-- Complexification of a physical configuration, without selecting any
real normal-mode basis. -/
def complexifyConfiguration {N : Nat} (q : HilbertConfiguration N) :
    Site N → Complex :=
  fun x ↦ (q x : Complex)

theorem complexForwardDifference_complexify
    {N : Nat} [NeZero N] (q : HilbertConfiguration N) (x : Site N) :
    complexForwardDifference (complexifyConfiguration q) x =
      (Lattice.forwardDifference (asConfiguration q) x : Complex) := by
  simp [complexForwardDifference, complexifyConfiguration,
    Lattice.forwardDifference, asConfiguration]

/-- The average-normalized character projection as a real-linear map on the
physical Hilbert configuration space. -/
def cycleFourierProjectionLinearMap
    (N : Nat) [NeZero N] (k : Site N) :
    HilbertConfiguration N →ₗ[Real] Complex where
  toFun q := cycleFourierCoefficient (complexifyConfiguration q) k
  map_add' q r := by
    rw [show complexifyConfiguration (q + r) =
        complexifyConfiguration q + complexifyConfiguration r by
      funext x
      simp [complexifyConfiguration]]
    exact cycleFourierCoefficient_add _ _ k
  map_smul' c q := by
    rw [show complexifyConfiguration (c • q) =
        (c : Complex) • complexifyConfiguration q by
      funext x
      simp [complexifyConfiguration]]
    simpa [Complex.real_smul] using
      cycleFourierCoefficient_smul (c : Complex)
        (complexifyConfiguration q) k

/-- Continuous version of the finite Fourier projection. -/
def cycleFourierProjectionCLM
    (N : Nat) [NeZero N] (k : Site N) :
    HilbertConfiguration N →L[Real] Complex :=
  LinearMap.toContinuousLinearMap (cycleFourierProjectionLinearMap N k)

@[simp] theorem cycleFourierProjectionCLM_apply
    (N : Nat) [NeZero N] (k : Site N) (q : HilbertConfiguration N) :
    cycleFourierProjectionCLM N k q =
      cycleFourierCoefficient (complexifyConfiguration q) k := rfl

theorem timeDeriv_cycleFourierProjection
    {N : Nat} [NeZero N] (k : Site N)
    (q : Time → HilbertConfiguration N) (t : Time)
    (hq : DifferentiableAt Real q t) :
    ∂ₜ (fun s ↦ cycleFourierProjectionCLM N k (q s)) t =
      cycleFourierProjectionCLM N k (∂ₜ q t) := by
  change fderiv Real (cycleFourierProjectionCLM N k ∘ q) t 1 =
    cycleFourierProjectionCLM N k (fderiv Real q t 1)
  rw [fderiv_comp]
  · simp
  · exact (cycleFourierProjectionCLM N k).differentiableAt
  · exact hq

/-- Complexified site force is exactly the outgoing divergence of the
linear-plus-quadratic bond stress. -/
theorem complexify_neg_potentialGradient_pureAlpha
    {N : Nat} [NeZero N] (alpha : Real)
    (q : HilbertConfiguration N) :
    complexifyConfiguration (-potentialGradient 1 0 alpha q) =
      complexOutgoingMinusIncoming
        (complexForwardDifference (complexifyConfiguration q) +
          (alpha : Complex) •
            fun x ↦ (complexForwardDifference
              (complexifyConfiguration q) x) ^ 2) := by
  funext i
  rw [show complexifyConfiguration (-potentialGradient 1 0 alpha q) i =
      ((-potentialGradient 1 0 alpha q) i : Complex) by rfl,
    neg_potentialGradient_pureAlpha_apply]
  simp only [complexOutgoingMinusIncoming, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [complexForwardDifference_complexify,
    complexForwardDifference_complexify]
  push_cast
  ring

/-- Exact Fourier projection of the pure-alpha Hamilton force.  The first
term is the clean-cycle harmonic force; the second is the finite convolution
with the exact bond symbols and no off-momentum contribution. -/
theorem cycleFourierProjection_neg_potentialGradient_pureAlpha
    {N : Nat} [NeZero N] (alpha : Real)
    (q : HilbertConfiguration N) (k : Site N) :
    cycleFourierProjectionCLM N k
        (-potentialGradient 1 0 alpha q) =
      -(cleanCycleModeEnergy N k : Complex) *
          cycleFourierProjectionCLM N k q +
        (alpha : Complex) * outgoingFourierSymbol N k *
          ∑ l : Site N,
            bondFourierSymbol N l * bondFourierSymbol N (k - l) *
              cycleFourierProjectionCLM N l q *
              cycleFourierProjectionCLM N (k - l) q := by
  simp only [cycleFourierProjectionCLM_apply]
  rw [complexify_neg_potentialGradient_pureAlpha,
    cycleFourierCoefficient_outgoingMinusIncoming,
    cycleFourierCoefficient_add,
    cycleFourierCoefficient_smul,
    cycleFourierCoefficient_forwardDifference,
    cycleFourierCoefficient_forwardDifference_sq]
  rw [show outgoingFourierSymbol N k *
      (bondFourierSymbol N k *
        cycleFourierCoefficient (complexifyConfiguration q) k +
        (alpha : Complex) *
          ∑ l : Site N,
            bondFourierSymbol N l * bondFourierSymbol N (k - l) *
              cycleFourierCoefficient (complexifyConfiguration q) l *
              cycleFourierCoefficient (complexifyConfiguration q) (k - l)) =
      (outgoingFourierSymbol N k * bondFourierSymbol N k) *
          cycleFourierCoefficient (complexifyConfiguration q) k +
        (alpha : Complex) * outgoingFourierSymbol N k *
          ∑ l : Site N,
            bondFourierSymbol N l * bondFourierSymbol N (k - l) *
              cycleFourierCoefficient (complexifyConfiguration q) l *
              cycleFourierCoefficient (complexifyConfiguration q) (k - l) by
        ring,
    outgoing_mul_bond_eq_neg_modeEnergy]

/-- The exact output/child coefficient in the quadratic Fourier force. -/
def pureAlphaQuadraticFourierCoefficient
    (N : Nat) [NeZero N] (alpha : Real)
    (k l : Site N) : Complex :=
  (alpha : Complex) * outgoingFourierSymbol N k *
    bondFourierSymbol N l * bondFourierSymbol N (k - l)

@[simp] theorem pureAlphaQuadraticFourierCoefficient_output_zero
    (N : Nat) [NeZero N] (alpha : Real) (l : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha 0 l = 0 := by
  simp [pureAlphaQuadraticFourierCoefficient]

@[simp] theorem pureAlphaQuadraticFourierCoefficient_left_zero
    (N : Nat) [NeZero N] (alpha : Real) (k : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha k 0 = 0 := by
  simp [pureAlphaQuadraticFourierCoefficient]

@[simp] theorem pureAlphaQuadraticFourierCoefficient_right_zero
    (N : Nat) [NeZero N] (alpha : Real) (k : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha k k = 0 := by
  simp [pureAlphaQuadraticFourierCoefficient]

/-- Exact complex Fourier modal equations for every differentiable trajectory
of the existing Physlib pure-alpha Hamilton system.  This is a finite-volume
identity and uses no phase, resonance, or kinetic closure hypothesis. -/
theorem pureAlpha_fourierModalEquations
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q) :
    (∀ t k,
      ∂ₜ (fun s ↦ cycleFourierProjectionCLM N k (q s)) t =
        cycleFourierProjectionCLM N k (p t)) ∧
    (∀ t k,
      ∂ₜ (fun s ↦ cycleFourierProjectionCLM N k (p s)) t =
        -(cleanCycleModeEnergy N k : Complex) *
            cycleFourierProjectionCLM N k (q t) +
          ∑ l : Site N,
            pureAlphaQuadraticFourierCoefficient N alpha k l *
              cycleFourierProjectionCLM N l (q t) *
              cycleFourierProjectionCLM N (k - l) (q t)) := by
  have hexplicit :=
    (satisfiesHamiltonEquations_iff_explicit
      (m := unitMassConfig N) (kappa := 1) (beta := 0) (g := alpha)
      (p := p) (q := q)).mp hHamilton
  constructor
  · intro t k
    rw [timeDeriv_cycleFourierProjection k q t (hq t),
      hexplicit.1 t, inverseMassMomentum_unitMass]
  · intro t k
    rw [timeDeriv_cycleFourierProjection k p t (hp t),
      hexplicit.2 t,
      cycleFourierProjection_neg_potentialGradient_pureAlpha]
    unfold pureAlphaQuadraticFourierCoefficient
    rw [Finset.mul_sum]
    apply congrArg ((-(cleanCycleModeEnergy N k : Complex) *
      cycleFourierProjectionCLM N k (q t)) + ·)
    apply Finset.sum_congr rfl
    intro l _hl
    ring

/-- The translation zero mode has zero projected force, including the
quadratic alpha term. -/
theorem cycleFourierProjection_neg_potentialGradient_pureAlpha_zero
    {N : Nat} [NeZero N] (alpha : Real)
    (q : HilbertConfiguration N) :
    cycleFourierProjectionCLM N 0
        (-potentialGradient 1 0 alpha q) = 0 := by
  rw [cycleFourierProjection_neg_potentialGradient_pureAlpha]
  simp [cleanCycleModeEnergy]

end

end ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
