import Mathlib
import ArchonPhysics.Lattice

/-!
# Equilibrium-distance Lennard--Jones bonds

This module records the Lennard--Jones 12--6 potential in the
equilibrium-distance parametrization

`D * ((r₀ / r)^12 - 2 * (r₀ / r)^6)`.

The shifted potential adds `D`, so its equilibrium value is zero when `r₀ ≠ 0`.
Physical bond
lengths are explicitly required to be positive; the algebraic formulas are
kept on `Real` so that they compose directly with the finite periodic lattice.

The local derivatives through order four identify the harmonic, cubic, and
quartic Taylor coefficients.  Since the exact potential contains both inverse
sixth and inverse-twelfth powers, this module makes no homogeneous
coupling-scaling claim.  `rescaledBondPotential` below is merely the exact
composition obtained by replacing the displacement by `g * x`.
-/

namespace ArchonPhysics.LennardJonesPotential

noncomputable section

/-- The equilibrium-distance Lennard--Jones 12--6 potential.  The parameter
`depth` is the well depth and `r₀` is the equilibrium distance. -/
def rawPotential (depth r₀ r : Real) : Real :=
  depth * ((r₀ / r) ^ 12 - 2 * (r₀ / r) ^ 6)

/-- The Lennard--Jones potential shifted so that its nonzero-equilibrium value is zero. -/
def shiftedPotential (depth r₀ r : Real) : Real :=
  rawPotential depth r₀ r + depth

/-- Physical admissibility of a radial separation. -/
def Admissible (r : Real) : Prop := 0 < r

/-- The shifted bond potential written in terms of displacement from `r₀`. -/
def bondPotential (depth r₀ x : Real) : Real :=
  shiftedPotential depth r₀ (r₀ + x)

/-- A displacement is admissible when its resulting physical bond length is
strictly positive. -/
def BondAdmissible (r₀ x : Real) : Prop :=
  Admissible (r₀ + x)

/-- An admissible displacement has a nonzero actual bond length. -/
theorem BondAdmissible.ne {r₀ x : Real} (h : BondAdmissible r₀ x) :
    r₀ + x ≠ 0 := by
  exact ne_of_gt h

/-- Exact composition with a displacement scale `g`.  This definition does
not assert a homogeneous power law in `g`. -/
def rescaledBondPotential (depth r₀ g x : Real) : Real :=
  bondPotential depth r₀ (g * x)

/-- The shifted potential is a manifest square. -/
theorem shiftedPotential_factor (depth r₀ r : Real) :
    shiftedPotential depth r₀ r =
      depth * (((r₀ / r) ^ 6 - 1) ^ 2) := by
  unfold shiftedPotential rawPotential
  ring

/-- A nonnegative well depth gives a nonnegative shifted potential. -/
theorem shiftedPotential_nonneg {depth r₀ r : Real} (hdepth : 0 ≤ depth) :
    0 ≤ shiftedPotential depth r₀ r := by
  rw [shiftedPotential_factor]
  positivity

/-- The raw potential takes value `-depth` at its nonzero equilibrium distance. -/
@[simp]
theorem rawPotential_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    rawPotential depth r₀ r₀ = -depth := by
  simp [rawPotential, hr₀]
  ring

/-- The shifted potential vanishes at its nonzero equilibrium distance. -/
@[simp]
theorem shiftedPotential_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    shiftedPotential depth r₀ r₀ = 0 := by
  simp [shiftedPotential, hr₀]

/-- The displacement bond potential vanishes at zero displacement. -/
@[simp]
theorem bondPotential_zero {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    bondPotential depth r₀ 0 = 0 := by
  simp [bondPotential, hr₀]

/-- Exact factorization after displacement rescaling.  In particular, this is
the correct replacement for a false homogeneous scaling assertion. -/
theorem rescaledBondPotential_factor (depth r₀ g x : Real) :
    rescaledBondPotential depth r₀ g x =
      depth * (((r₀ / (r₀ + g * x)) ^ 6 - 1) ^ 2) := by
  rw [rescaledBondPotential, bondPotential, shiftedPotential_factor]

/-- The first radial derivative of the raw/shifted potential. -/
def radialDerivative (depth r₀ r : Real) : Real :=
  12 * depth * (r₀ ^ 6 / r ^ 7 - r₀ ^ 12 / r ^ 13)

/-- The second radial derivative. -/
def radialSecondDerivative (depth r₀ r : Real) : Real :=
  12 * depth * (13 * r₀ ^ 12 / r ^ 14 - 7 * r₀ ^ 6 / r ^ 8)

/-- The third radial derivative. -/
def radialThirdDerivative (depth r₀ r : Real) : Real :=
  12 * depth * (56 * r₀ ^ 6 / r ^ 9 - 182 * r₀ ^ 12 / r ^ 15)

/-- The fourth radial derivative. -/
def radialFourthDerivative (depth r₀ r : Real) : Real :=
  12 * depth * (2730 * r₀ ^ 12 / r ^ 16 - 504 * r₀ ^ 6 / r ^ 10)

/-- The raw Lennard--Jones potential has the stated derivative away from its
singular separation. -/
theorem hasDerivAt_rawPotential {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (rawPotential depth r₀) (radialDerivative depth r₀ r) r := by
  have hbase := (hasDerivAt_const r r₀).div (hasDerivAt_id r) hr
  have heq : (fun s : Real => r₀ / s) =ᶠ[nhds r]
      ((fun _ => r₀) / id) := by
    filter_upwards with s
    rfl
  have hquotientRaw := hbase.congr_of_eventuallyEq heq
  have hquotient :
      HasDerivAt (fun s : Real => r₀ / s) (-r₀ / r ^ 2) r := by
    apply hquotientRaw.congr_deriv
    simp only [id_eq, zero_mul, mul_one, zero_sub]
  have h12 := hquotient.pow 12
  have h6 := hquotient.pow 6
  have h := (hasDerivAt_const r depth).mul
    (h12.sub ((hasDerivAt_const r 2).mul h6))
  have hfun : rawPotential depth r₀ =ᶠ[nhds r]
      ((fun _ => depth) * ((fun s => r₀ / s) ^ 12 -
        (fun _ => 2) * (fun s => r₀ / s) ^ 6)) := by
    filter_upwards with s
    rfl
  have h' := h.congr_of_eventuallyEq hfun
  apply h'.congr_deriv
  unfold radialDerivative
  simp only [Nat.cast_ofNat, zero_mul, zero_add]
  norm_num
  rw [div_pow, div_pow]
  field_simp [hr]
  ring

/-- Adding the constant well-depth shift leaves the derivative unchanged. -/
theorem hasDerivAt_shiftedPotential {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (shiftedPotential depth r₀) (radialDerivative depth r₀ r) r := by
  change HasDerivAt (fun s => rawPotential depth r₀ s + depth)
    (radialDerivative depth r₀ r) r
  exact (hasDerivAt_rawPotential (depth := depth) (r₀ := r₀) hr).add_const depth

/-- The displacement bond potential has the radial derivative evaluated at
its actual bond length, whenever that length is nonzero. -/
theorem hasDerivAt_bondPotential_of_ne {depth r₀ x : Real}
    (hbond : r₀ + x ≠ 0) :
    HasDerivAt (bondPotential depth r₀)
      (radialDerivative depth r₀ (r₀ + x)) x := by
  have hinnerBase := (hasDerivAt_const x r₀).add (hasDerivAt_id x)
  have hinnerEq : (fun y : Real => r₀ + y) =ᶠ[nhds x]
      ((fun _ => r₀) + id) := by
    filter_upwards with y
    rfl
  have hinnerRaw := hinnerBase.congr_of_eventuallyEq hinnerEq
  have hinner : HasDerivAt (fun y : Real => r₀ + y) 1 x := by
    apply hinnerRaw.congr_deriv
    simp only [zero_add]
  have hcomp :=
    (hasDerivAt_shiftedPotential (depth := depth) (r₀ := r₀) hbond).comp x hinner
  have heq : bondPotential depth r₀ =ᶠ[nhds x]
      shiftedPotential depth r₀ ∘ (fun y => r₀ + y) := by
    filter_upwards with y
    rfl
  have h := hcomp.congr_of_eventuallyEq heq
  apply h.congr_deriv
  ring

/-- Physical bond admissibility supplies the nonsingularity needed for the
bond derivative formula. -/
theorem hasDerivAt_bondPotential {depth r₀ x : Real}
    (hbond : BondAdmissible r₀ x) :
    HasDerivAt (bondPotential depth r₀)
      (radialDerivative depth r₀ (r₀ + x)) x :=
  hasDerivAt_bondPotential_of_ne hbond.ne

/-- Differentiating the explicit first-derivative formula. -/
theorem hasDerivAt_radialDerivative {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (radialDerivative depth r₀)
      (radialSecondDerivative depth r₀ r) r := by
  have h7base := (hasDerivAt_const r (r₀ ^ 6)).div
    ((hasDerivAt_id r).pow 7) (pow_ne_zero 7 hr)
  have h7eq : (fun s : Real => r₀ ^ 6 / s ^ 7) =ᶠ[nhds r]
      ((fun _ => r₀ ^ 6) / id ^ 7) := by
    filter_upwards with s
    rfl
  have h7raw := h7base.congr_of_eventuallyEq h7eq
  have h7 : HasDerivAt (fun s : Real => r₀ ^ 6 / s ^ 7)
      (-7 * r₀ ^ 6 / r ^ 8) r := by
    apply h7raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
  have h13base := (hasDerivAt_const r (r₀ ^ 12)).div
    ((hasDerivAt_id r).pow 13) (pow_ne_zero 13 hr)
  have h13eq : (fun s : Real => r₀ ^ 12 / s ^ 13) =ᶠ[nhds r]
      ((fun _ => r₀ ^ 12) / id ^ 13) := by
    filter_upwards with s
    rfl
  have h13raw := h13base.congr_of_eventuallyEq h13eq
  have h13 : HasDerivAt (fun s : Real => r₀ ^ 12 / s ^ 13)
      (-13 * r₀ ^ 12 / r ^ 14) r := by
    apply h13raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
  have h := (hasDerivAt_const r (12 * depth)).mul (h7.sub h13)
  have heq : radialDerivative depth r₀ =ᶠ[nhds r]
      ((fun _ => 12 * depth) *
        ((fun s => r₀ ^ 6 / s ^ 7) - fun s => r₀ ^ 12 / s ^ 13)) := by
    filter_upwards with s
    rfl
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  unfold radialSecondDerivative
  simp only [zero_mul, zero_add]
  ring

/-- Differentiating the explicit second-derivative formula. -/
theorem hasDerivAt_radialSecondDerivative {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (radialSecondDerivative depth r₀)
      (radialThirdDerivative depth r₀ r) r := by
  have h14base := (hasDerivAt_const r (13 * r₀ ^ 12)).div
    ((hasDerivAt_id r).pow 14) (pow_ne_zero 14 hr)
  have h14eq : (fun s : Real => 13 * r₀ ^ 12 / s ^ 14) =ᶠ[nhds r]
      ((fun _ => 13 * r₀ ^ 12) / id ^ 14) := by
    filter_upwards with s
    rfl
  have h14raw := h14base.congr_of_eventuallyEq h14eq
  have h14 : HasDerivAt (fun s : Real => 13 * r₀ ^ 12 / s ^ 14)
      (-182 * r₀ ^ 12 / r ^ 15) r := by
    apply h14raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
    ring
  have h8base := (hasDerivAt_const r (7 * r₀ ^ 6)).div
    ((hasDerivAt_id r).pow 8) (pow_ne_zero 8 hr)
  have h8eq : (fun s : Real => 7 * r₀ ^ 6 / s ^ 8) =ᶠ[nhds r]
      ((fun _ => 7 * r₀ ^ 6) / id ^ 8) := by
    filter_upwards with s
    rfl
  have h8raw := h8base.congr_of_eventuallyEq h8eq
  have h8 : HasDerivAt (fun s : Real => 7 * r₀ ^ 6 / s ^ 8)
      (-56 * r₀ ^ 6 / r ^ 9) r := by
    apply h8raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
    ring
  have h := (hasDerivAt_const r (12 * depth)).mul (h14.sub h8)
  have heq : radialSecondDerivative depth r₀ =ᶠ[nhds r]
      ((fun _ => 12 * depth) *
        ((fun s => 13 * r₀ ^ 12 / s ^ 14) -
          fun s => 7 * r₀ ^ 6 / s ^ 8)) := by
    filter_upwards with s
    rfl
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  unfold radialThirdDerivative
  simp only [zero_mul, zero_add]
  ring

/-- Differentiating the explicit third-derivative formula. -/
theorem hasDerivAt_radialThirdDerivative {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (radialThirdDerivative depth r₀)
      (radialFourthDerivative depth r₀ r) r := by
  have h9base := (hasDerivAt_const r (56 * r₀ ^ 6)).div
    ((hasDerivAt_id r).pow 9) (pow_ne_zero 9 hr)
  have h9eq : (fun s : Real => 56 * r₀ ^ 6 / s ^ 9) =ᶠ[nhds r]
      ((fun _ => 56 * r₀ ^ 6) / id ^ 9) := by
    filter_upwards with s
    rfl
  have h9raw := h9base.congr_of_eventuallyEq h9eq
  have h9 : HasDerivAt (fun s : Real => 56 * r₀ ^ 6 / s ^ 9)
      (-504 * r₀ ^ 6 / r ^ 10) r := by
    apply h9raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
    ring
  have h15base := (hasDerivAt_const r (182 * r₀ ^ 12)).div
    ((hasDerivAt_id r).pow 15) (pow_ne_zero 15 hr)
  have h15eq : (fun s : Real => 182 * r₀ ^ 12 / s ^ 15) =ᶠ[nhds r]
      ((fun _ => 182 * r₀ ^ 12) / id ^ 15) := by
    filter_upwards with s
    rfl
  have h15raw := h15base.congr_of_eventuallyEq h15eq
  have h15 : HasDerivAt (fun s : Real => 182 * r₀ ^ 12 / s ^ 15)
      (-2730 * r₀ ^ 12 / r ^ 16) r := by
    apply h15raw.congr_deriv
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, zero_mul, mul_one, zero_sub]
    field_simp [hr]
    ring
  have h := (hasDerivAt_const r (12 * depth)).mul (h9.sub h15)
  have heq : radialThirdDerivative depth r₀ =ᶠ[nhds r]
      ((fun _ => 12 * depth) *
        ((fun s => 56 * r₀ ^ 6 / s ^ 9) -
          fun s => 182 * r₀ ^ 12 / s ^ 15)) := by
    filter_upwards with s
    rfl
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  unfold radialFourthDerivative
  simp only [zero_mul, zero_add]
  ring

/-- The equilibrium is stationary. -/
@[simp]
theorem radialDerivative_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    radialDerivative depth r₀ r₀ = 0 := by
  unfold radialDerivative
  field_simp [hr₀]
  ring

/-- The raw potential has zero derivative at a nonzero equilibrium distance. -/
theorem hasDerivAt_rawPotential_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    HasDerivAt (rawPotential depth r₀) 0 r₀ := by
  simpa [radialDerivative_equilibrium hr₀] using
    hasDerivAt_rawPotential (depth := depth) (r₀ := r₀) hr₀

/-- The shifted potential has zero derivative at a nonzero equilibrium distance. -/
theorem hasDerivAt_shiftedPotential_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    HasDerivAt (shiftedPotential depth r₀) 0 r₀ := by
  simpa [radialDerivative_equilibrium hr₀] using
    hasDerivAt_shiftedPotential (depth := depth) (r₀ := r₀) hr₀

/-- The displacement bond potential is stationary at zero displacement. -/
theorem hasDerivAt_bondPotential_zero {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    HasDerivAt (bondPotential depth r₀) 0 0 := by
  have h := hasDerivAt_bondPotential_of_ne
    (depth := depth) (x := 0) (by simpa using hr₀)
  simpa [radialDerivative_equilibrium hr₀] using h

/-- Exact curvature at equilibrium. -/
@[simp]
theorem radialSecondDerivative_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    radialSecondDerivative depth r₀ r₀ = 72 * depth / r₀ ^ 2 := by
  unfold radialSecondDerivative
  field_simp [hr₀]
  ring

/-- Exact third derivative at equilibrium. -/
@[simp]
theorem radialThirdDerivative_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    radialThirdDerivative depth r₀ r₀ = -1512 * depth / r₀ ^ 3 := by
  unfold radialThirdDerivative
  field_simp [hr₀]
  ring

/-- Exact fourth derivative at equilibrium. -/
@[simp]
theorem radialFourthDerivative_equilibrium {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    radialFourthDerivative depth r₀ r₀ = 26712 * depth / r₀ ^ 4 := by
  unfold radialFourthDerivative
  field_simp [hr₀]
  ring

/-- Harmonic stiffness in the local displacement expansion. -/
def harmonicStiffness (depth r₀ : Real) : Real :=
  72 * depth / r₀ ^ 2

/-- Coefficient of `x^2` in the ordinary Taylor polynomial. -/
def quadraticTaylorCoefficient (depth r₀ : Real) : Real :=
  36 * depth / r₀ ^ 2

/-- Coefficient of `x^3` in the ordinary Taylor polynomial. -/
def cubicTaylorCoefficient (depth r₀ : Real) : Real :=
  -252 * depth / r₀ ^ 3

/-- Coefficient of `x^4` in the ordinary Taylor polynomial. -/
def quarticTaylorCoefficient (depth r₀ : Real) : Real :=
  1113 * depth / r₀ ^ 4

/-- The local FPUT-alpha coefficient in the convention `alpha*x^3/3`. -/
def alphaCoefficient (depth r₀ : Real) : Real :=
  -756 * depth / r₀ ^ 3

/-- The local FPUT-beta coefficient in the convention `beta*x^4/4`. -/
def betaCoefficient (depth r₀ : Real) : Real :=
  4452 * depth / r₀ ^ 4

/-- Fourth-order local FPUT polynomial determined by the LJ derivatives. -/
def localAlphaBetaPotential (depth r₀ x : Real) : Real :=
  harmonicStiffness depth r₀ * x ^ 2 / 2 +
    alphaCoefficient depth r₀ * x ^ 3 / 3 +
    betaCoefficient depth r₀ * x ^ 4 / 4

/-- The Taylor and FPUT normalizations give identical coefficients. -/
theorem localAlphaBetaPotential_eq_taylor (depth r₀ x : Real) :
    localAlphaBetaPotential depth r₀ x =
      quadraticTaylorCoefficient depth r₀ * x ^ 2 +
      cubicTaylorCoefficient depth r₀ * x ^ 3 +
      quarticTaylorCoefficient depth r₀ * x ^ 4 := by
  unfold localAlphaBetaPotential harmonicStiffness alphaCoefficient betaCoefficient
  unfold quadraticTaylorCoefficient cubicTaylorCoefficient quarticTaylorCoefficient
  ring

/-- The quadratic Taylor coefficient is one half of the equilibrium curvature. -/
theorem quadraticTaylorCoefficient_eq_half_secondDerivative
    {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    quadraticTaylorCoefficient depth r₀ =
      radialSecondDerivative depth r₀ r₀ / 2 := by
  rw [radialSecondDerivative_equilibrium hr₀]
  unfold quadraticTaylorCoefficient
  ring

/-- The cubic Taylor coefficient is one sixth of the equilibrium third derivative. -/
theorem cubicTaylorCoefficient_eq_sixth_thirdDerivative
    {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    cubicTaylorCoefficient depth r₀ =
      radialThirdDerivative depth r₀ r₀ / 6 := by
  rw [radialThirdDerivative_equilibrium hr₀]
  unfold cubicTaylorCoefficient
  ring

/-- The quartic Taylor coefficient is one twenty-fourth of the equilibrium
fourth derivative. -/
theorem quarticTaylorCoefficient_eq_twentyFourth_fourthDerivative
    {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    quarticTaylorCoefficient depth r₀ =
      radialFourthDerivative depth r₀ r₀ / 24 := by
  rw [radialFourthDerivative_equilibrium hr₀]
  unfold quarticTaylorCoefficient
  ring

/-- The local alpha coefficient is three times the ordinary cubic coefficient. -/
theorem alphaCoefficient_eq_three_mul_cubic (depth r₀ : Real) :
    alphaCoefficient depth r₀ = 3 * cubicTaylorCoefficient depth r₀ := by
  unfold alphaCoefficient cubicTaylorCoefficient
  ring

/-- The local beta coefficient is four times the ordinary quartic coefficient. -/
theorem betaCoefficient_eq_four_mul_quartic (depth r₀ : Real) :
    betaCoefficient depth r₀ = 4 * quarticTaylorCoefficient depth r₀ := by
  unfold betaCoefficient quarticTaylorCoefficient
  ring

/-- A periodic configuration is LJ-admissible when every actual nearest-neighbour
bond length is strictly positive. -/
def AdmissibleConfiguration {N : Nat} (r₀ : Real)
    (q : Lattice.Configuration N) : Prop :=
  ∀ i : Lattice.Site N, BondAdmissible r₀ (Lattice.forwardDifference q i)

/-- Potential energy of a periodic LJ chain, normalized to vanish at equilibrium. -/
def periodicPotentialEnergy {N : Nat} [NeZero N] (depth r₀ : Real)
    (q : Lattice.Configuration N) : Real :=
  ∑ i : Lattice.Site N,
    bondPotential depth r₀ (Lattice.forwardDifference q i)

/-- The finite periodic random-mass Hamiltonian for a frozen positive mass
realization.  Randomness enters through `m`; this deterministic function can be
composed with any random mass ensemble. -/
def periodicRandomMassHamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Lattice.Configuration N) : Real :=
  Lattice.kineticEnergy m p + periodicPotentialEnergy depth r₀ q

/-- Formula-level expansion of the periodic LJ Hamiltonian. -/
theorem periodicRandomMassHamiltonian_spec {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Lattice.Configuration N) :
    periodicRandomMassHamiltonian m depth r₀ p q =
      (∑ i : Lattice.Site N, p i ^ 2 / (2 * m.mass i)) +
      ∑ i : Lattice.Site N,
        shiftedPotential depth r₀
          (r₀ + Lattice.forwardDifference q i) := by
  rfl

/-- Nonnegative well depth makes every shifted periodic LJ potential energy
nonnegative. -/
theorem periodicPotentialEnergy_nonneg {N : Nat} [NeZero N]
    {depth r₀ : Real} (hdepth : 0 ≤ depth) (q : Lattice.Configuration N) :
    0 ≤ periodicPotentialEnergy depth r₀ q := by
  unfold periodicPotentialEnergy
  exact Finset.sum_nonneg fun i _ => shiftedPotential_nonneg hdepth

/-- The full finite Hamiltonian is nonnegative for nonnegative well depth. -/
theorem periodicRandomMassHamiltonian_nonneg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {depth r₀ : Real}
    (hdepth : 0 ≤ depth) (p q : Lattice.Configuration N) :
    0 ≤ periodicRandomMassHamiltonian m depth r₀ p q := by
  unfold periodicRandomMassHamiltonian
  exact add_nonneg (Lattice.kineticEnergy_nonneg m p)
    (periodicPotentialEnergy_nonneg hdepth q)

/-- Pointwise form of configuration admissibility. -/
theorem admissibleConfiguration_iff {N : Nat} (r₀ : Real)
    (q : Lattice.Configuration N) :
    AdmissibleConfiguration r₀ q ↔
      ∀ i : Lattice.Site N, 0 < r₀ + Lattice.forwardDifference q i := by
  rfl

end

end ArchonPhysics.LennardJonesPotential
