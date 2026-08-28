import ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian

/-!
# An explicit finite atlas for the nondegenerate Umklapp shell

For fixed principal-zone external momenta, the moving angle

`theta = (2 * k₂ - k₀ - k₁) / 4`

lies in `(-pi, pi)`.  Removing the two cosine zeros splits this interval into
three explicit monotonicity patches.  This file packages those three patches
as a finite atlas, classifies every derivative-degenerate point in the open
Brillouin zone, and places every positive-discriminant resonant root in an
explicit smaller closed interval on which the derivative has one strict
sign.

The construction is finite-dimensional trigonometric geometry.  It assumes
neither a kinetic equation nor a random-phase closure.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

noncomputable section

/-! ## Principal-zone phase bounds and exact degeneracy classification -/

/-- Moving sine/cosine angle in the reduced Umklapp formula. -/
def umklappMovingAngle (k₀ k₁ k₂ : Real) : Real :=
  (2 * k₂ - k₀ - k₁) / 4

theorem umklappMovingAngle_mem_Ioo_neg_pi_pi
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    umklappMovingAngle k₀ k₁ k₂ ∈ Ioo (-Real.pi) Real.pi := by
  unfold umklappMovingAngle
  constructor <;> linarith

theorem structuralUmklappAngle_mem_Ioo_zero_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    (k₀ + k₁) / 4 ∈ Ioo 0 Real.pi := by
  constructor <;> linarith

private theorem cos_eq_zero_iff_of_mem_Ioo_neg_pi_pi
    {x : Real} (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    Real.cos x = 0 ↔ x = -(Real.pi / 2) ∨ x = Real.pi / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy x (-(Real.pi / 2)) with hlower | heqLower | haboveLower
    · have hneg : Real.cos x < 0 := by
        rw [← Real.cos_neg x]
        exact Real.cos_neg_of_pi_div_two_lt_of_lt
          (by linarith) (by linarith [hx.1])
      linarith
    · exact Or.inl heqLower
    · rcases lt_trichotomy x (Real.pi / 2) with hcentral | heqUpper | hupper
      · have hpos : 0 < Real.cos x :=
          Real.cos_pos_of_mem_Ioo ⟨haboveLower, hcentral⟩
        linarith
      · exact Or.inr heqUpper
      · have hneg : Real.cos x < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt hupper (by linarith [hx.2])
        linarith
  · rintro (rfl | rfl) <;> simp

private theorem cos_eq_zero_iff_of_mem_Ioo_zero_pi
    {x : Real} (hx : x ∈ Ioo 0 Real.pi) :
    Real.cos x = 0 ↔ x = Real.pi / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy x (Real.pi / 2) with hlower | heq | hupper
    · have hpos : 0 < Real.cos x :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], hlower⟩
      linarith
    · exact heq
    · have hneg : Real.cos x < 0 :=
          Real.cos_neg_of_pi_div_two_lt_of_lt hupper (by linarith [hx.2])
      linarith
  · rintro rfl
    simp

/-- In the open principal Brillouin zone the full periodic degeneracy set
reduces to one structural line and the two explicit moving critical lines. -/
theorem umklappK₂DerivativeDegenerate_iff_principal_critical_lines
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      k₀ + k₁ = 2 * Real.pi ∨
        k₂ = (k₀ + k₁) / 2 - Real.pi ∨
        k₂ = (k₀ + k₁) / 2 + Real.pi := by
  rw [umklappK₂DerivativeDegenerate_iff_cosine_factor]
  have hstruct := structuralUmklappAngle_mem_Ioo_zero_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi
  have hmoving := umklappMovingAngle_mem_Ioo_neg_pi_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi
  rw [cos_eq_zero_iff_of_mem_Ioo_zero_pi hstruct]
  change (k₀ + k₁) / 4 = Real.pi / 2 ∨
      Real.cos (umklappMovingAngle k₀ k₁ k₂) = 0 ↔ _
  rw [cos_eq_zero_iff_of_mem_Ioo_neg_pi_pi hmoving]
  unfold umklappMovingAngle
  constructor
  · rintro (hstructural | hlower | hupper)
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  · rintro (hstructural | hlower | hupper)
    · left; linarith
    · right; left; linarith
    · right; right; linarith

/-- The same classification with the principal-zone location of each moving
critical line made explicit. -/
theorem umklappK₂DerivativeDegenerate_iff_principal_ordered
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      k₀ + k₁ = 2 * Real.pi ∨
        (2 * Real.pi < k₀ + k₁ ∧
          k₂ = (k₀ + k₁) / 2 - Real.pi) ∨
        (k₀ + k₁ < 2 * Real.pi ∧
          k₂ = (k₀ + k₁) / 2 + Real.pi) := by
  rw [umklappK₂DerivativeDegenerate_iff_principal_critical_lines
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi]
  constructor
  · rintro (hstructural | hlower | hupper)
    · exact Or.inl hstructural
    · right; left
      constructor
      · linarith
      · exact hlower
    · right; right
      constructor
      · linarith
      · exact hupper
  · rintro (hstructural | ⟨_hsum, hlower⟩ | ⟨_hsum, hupper⟩)
    · exact Or.inl hstructural
    · exact Or.inr (Or.inl hlower)
    · exact Or.inr (Or.inr hupper)

/-! ## Three explicit monotonicity patches -/

inductive UmklappAtlasBranch
  | lower
  | central
  | upper
  deriving DecidableEq

instance : Fintype UmklappAtlasBranch where
  elems := {.lower, .central, .upper}
  complete := by
    intro branch
    cases branch <;> simp

@[simp] theorem card_umklappAtlasBranch :
    Fintype.card UmklappAtlasBranch = 3 := by
  decide

def umklappAtlasLeftEndpoint
    (branch : UmklappAtlasBranch) (k₀ k₁ : Real) : Real :=
  match branch with
  | .lower => (k₀ + k₁) / 2 - 2 * Real.pi
  | .central => (k₀ + k₁) / 2 - Real.pi
  | .upper => (k₀ + k₁) / 2 + Real.pi

def umklappAtlasRightEndpoint
    (branch : UmklappAtlasBranch) (k₀ k₁ : Real) : Real :=
  match branch with
  | .lower => (k₀ + k₁) / 2 - Real.pi
  | .central => (k₀ + k₁) / 2 + Real.pi
  | .upper => (k₀ + k₁) / 2 + 2 * Real.pi

/-- One of the three open moving-angle components cut out by the two
derivative-degenerate cosine zeros in `(-pi, pi)`. -/
def umklappAtlasPatch
    (branch : UmklappAtlasBranch) (k₀ k₁ : Real) : Set Real :=
  Ioo (umklappAtlasLeftEndpoint branch k₀ k₁)
    (umklappAtlasRightEndpoint branch k₀ k₁)

theorem umklappAtlasPatch_isOpen
    (branch : UmklappAtlasBranch) (k₀ k₁ : Real) :
    IsOpen (umklappAtlasPatch branch k₀ k₁) :=
  isOpen_Ioo

theorem umklappAtlasPatch_angle
    {branch : UmklappAtlasBranch} {k₀ k₁ k₂ : Real} :
    k₂ ∈ umklappAtlasPatch branch k₀ k₁ ↔
      match branch with
      | .lower => umklappMovingAngle k₀ k₁ k₂ ∈
          Ioo (-Real.pi) (-(Real.pi / 2))
      | .central => umklappMovingAngle k₀ k₁ k₂ ∈
          Ioo (-(Real.pi / 2)) (Real.pi / 2)
      | .upper => umklappMovingAngle k₀ k₁ k₂ ∈
          Ioo (Real.pi / 2) Real.pi := by
  cases branch <;>
    simp only [umklappAtlasPatch, umklappAtlasLeftEndpoint,
      umklappAtlasRightEndpoint, umklappMovingAngle, mem_Ioo] <;>
    constructor <;> rintro ⟨hleft, hright⟩ <;>
    constructor <;> linarith

theorem movingCosine_sign_on_umklappAtlasPatch
    (branch : UmklappAtlasBranch) (k₀ k₁ : Real) :
    (branch = .central ∧
      ∀ k₂ ∈ umklappAtlasPatch branch k₀ k₁,
        0 < Real.cos (umklappMovingAngle k₀ k₁ k₂)) ∨
    (branch ≠ .central ∧
      ∀ k₂ ∈ umklappAtlasPatch branch k₀ k₁,
        Real.cos (umklappMovingAngle k₀ k₁ k₂) < 0) := by
  cases branch
  · right
    constructor
    · simp
    · intro k₂ hk₂
      rw [umklappAtlasPatch_angle] at hk₂
      change umklappMovingAngle k₀ k₁ k₂ ∈
        Ioo (-Real.pi) (-(Real.pi / 2)) at hk₂
      rw [← Real.cos_neg]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt
        (by linarith [hk₂.2]) (by linarith [hk₂.1, Real.pi_pos])
  · left
    constructor
    · rfl
    · intro k₂ hk₂
      rw [umklappAtlasPatch_angle] at hk₂
      exact Real.cos_pos_of_mem_Ioo hk₂
  · right
    constructor
    · simp
    · intro k₂ hk₂
      rw [umklappAtlasPatch_angle] at hk₂
      change umklappMovingAngle k₀ k₁ k₂ ∈
        Ioo (Real.pi / 2) Real.pi at hk₂
      exact Real.cos_neg_of_pi_div_two_lt_of_lt hk₂.1
        (by linarith [hk₂.2, Real.pi_pos])

/-- On each atlas patch the derivative has one strict sign as soon as the
fixed structural cosine is nonzero. -/
theorem umklappK₂DerivativeFactor_fixedSign_on_atlasPatch
    {k₀ k₁ : Real}
    (hstructural : umklappResonanceDenominator k₀ k₁ ≠ 0)
    (branch : UmklappAtlasBranch) :
    (∀ k₂ ∈ umklappAtlasPatch branch k₀ k₁,
        0 < umklappK₂DerivativeFactor k₀ k₁ k₂) ∨
      (∀ k₂ ∈ umklappAtlasPatch branch k₀ k₁,
        umklappK₂DerivativeFactor k₀ k₁ k₂ < 0) := by
  have hstructural' : Real.cos ((k₀ + k₁) / 4) ≠ 0 := by
    simpa [umklappResonanceDenominator] using hstructural
  rcases lt_or_gt_of_ne hstructural' with hstructNeg | hstructPos
  · rcases movingCosine_sign_on_umklappAtlasPatch branch k₀ k₁ with
      ⟨hcentral, hcosPos⟩ | ⟨houter, hcosNeg⟩
    · left
      intro k₂ hk₂
      rw [umklappK₂DerivativeFactor]
      exact mul_pos (mul_pos_of_neg_of_neg (by linarith) hstructNeg)
        (hcosPos k₂ hk₂)
    · right
      intro k₂ hk₂
      rw [umklappK₂DerivativeFactor]
      exact mul_neg_of_pos_of_neg
        (mul_pos_of_neg_of_neg (by linarith) hstructNeg)
        (hcosNeg k₂ hk₂)
  · rcases movingCosine_sign_on_umklappAtlasPatch branch k₀ k₁ with
      ⟨hcentral, hcosPos⟩ | ⟨houter, hcosNeg⟩
    · right
      intro k₂ hk₂
      rw [umklappK₂DerivativeFactor]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by linarith) hstructPos)
        (hcosPos k₂ hk₂)
    · left
      intro k₂ hk₂
      rw [umklappK₂DerivativeFactor]
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (by linarith) hstructPos)
        (hcosNeg k₂ hk₂)

/-- The three explicit patches cover every nondegenerate principal-zone
point. -/
theorem exists_umklappAtlasBranch_of_nondegenerate
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hnondegenerate : ¬ UmklappK₂DerivativeDegenerate k₀ k₁ k₂) :
    ∃ branch : UmklappAtlasBranch,
      k₂ ∈ umklappAtlasPatch branch k₀ k₁ := by
  have hangle := umklappMovingAngle_mem_Ioo_neg_pi_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi
  have hcos : Real.cos (umklappMovingAngle k₀ k₁ k₂) ≠ 0 := by
    intro hzero
    apply hnondegenerate
    rw [umklappK₂DerivativeDegenerate_iff_cosine_factor]
    exact Or.inr hzero
  rcases lt_trichotomy (umklappMovingAngle k₀ k₁ k₂)
      (-(Real.pi / 2)) with hlower | heqLower | haboveLower
  · exact ⟨.lower, (umklappAtlasPatch_angle).2 ⟨hangle.1, hlower⟩⟩
  · exfalso
    apply hcos
    rw [heqLower]
    simp
  · rcases lt_trichotomy (umklappMovingAngle k₀ k₁ k₂)
        (Real.pi / 2) with hcentral | heqUpper | hupper
    · exact ⟨.central,
        (umklappAtlasPatch_angle).2 ⟨haboveLower, hcentral⟩⟩
    · exfalso
      apply hcos
      rw [heqUpper]
      simp
    · exact ⟨.upper, (umklappAtlasPatch_angle).2 ⟨hupper, hangle.2⟩⟩

/-! ## Explicit local closed intervals around nondegenerate roots -/

def umklappAtlasLocalLeft
    (branch : UmklappAtlasBranch) (k₀ k₁ root : Real) : Real :=
  (umklappAtlasLeftEndpoint branch k₀ k₁ + root) / 2

def umklappAtlasLocalRight
    (branch : UmklappAtlasBranch) (k₀ k₁ root : Real) : Real :=
  (root + umklappAtlasRightEndpoint branch k₀ k₁) / 2

theorem root_mem_umklappAtlasLocalInterval
    {branch : UmklappAtlasBranch} {k₀ k₁ root : Real}
    (hroot : root ∈ umklappAtlasPatch branch k₀ k₁) :
    root ∈ Ioo (umklappAtlasLocalLeft branch k₀ k₁ root)
      (umklappAtlasLocalRight branch k₀ k₁ root) := by
  unfold umklappAtlasPatch at hroot
  rcases hroot with ⟨hleft, hright⟩
  unfold umklappAtlasLocalLeft umklappAtlasLocalRight
  constructor <;> linarith

theorem umklappAtlasLocalIcc_subset_patch
    {branch : UmklappAtlasBranch} {k₀ k₁ root : Real}
    (hroot : root ∈ umklappAtlasPatch branch k₀ k₁) :
    Icc (umklappAtlasLocalLeft branch k₀ k₁ root)
        (umklappAtlasLocalRight branch k₀ k₁ root) ⊆
      umklappAtlasPatch branch k₀ k₁ := by
  intro z hz
  unfold umklappAtlasPatch at hroot ⊢
  rcases hroot with ⟨hrootLeft, hrootRight⟩
  unfold umklappAtlasLocalLeft umklappAtlasLocalRight at hz
  rcases hz with ⟨hzLeft, hzRight⟩
  constructor <;> linarith

/-- Every positive-discriminant resonant root belongs to one of the three
finite atlas patches and to an explicit smaller closed interval on which the
actual derivative has one strict sign. -/
theorem positiveDiscriminant_resonantRoot_has_explicit_fixedSign_interval
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    ∃ branch : UmklappAtlasBranch,
      k₂ ∈ Ioo (umklappAtlasLocalLeft branch k₀ k₁ k₂)
          (umklappAtlasLocalRight branch k₀ k₁ k₂) ∧
      ((∀ z ∈ Icc (umklappAtlasLocalLeft branch k₀ k₁ k₂)
              (umklappAtlasLocalRight branch k₀ k₁ k₂),
            0 < umklappK₂DerivativeFactor k₀ k₁ z) ∨
        (∀ z ∈ Icc (umklappAtlasLocalLeft branch k₀ k₁ k₂)
              (umklappAtlasLocalRight branch k₀ k₁ k₂),
            umklappK₂DerivativeFactor k₀ k₁ z < 0)) := by
  have hnondegenerate :
      ¬ UmklappK₂DerivativeDegenerate k₀ k₁ k₂ := by
    exact umklappK₂DerivativeFactor_ne_zero_of_resonant
      hdisc hresonant
  obtain ⟨branch, hbranch⟩ := exists_umklappAtlasBranch_of_nondegenerate
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi hnondegenerate
  have hdenominator : umklappResonanceDenominator k₀ k₁ ≠ 0 := by
    intro hzero
    have hdisc' := (umklappTransverseDiscriminant_pos_iff k₀ k₁).1 hdisc
    rw [hzero, abs_zero] at hdisc'
    exact (not_lt_of_ge (abs_nonneg _)) hdisc'
  refine ⟨branch, root_mem_umklappAtlasLocalInterval hbranch, ?_⟩
  rcases umklappK₂DerivativeFactor_fixedSign_on_atlasPatch
      hdenominator branch with hpositive | hnegative
  · left
    intro z hz
    exact hpositive z (umklappAtlasLocalIcc_subset_patch hbranch hz)
  · right
    intro z hz
    exact hnegative z (umklappAtlasLocalIcc_subset_patch hbranch hz)

/-! ## Two explicit arcsine branches -/

/-- Dimensionless right-hand side of the on-shell sine equation. -/
def umklappResonanceRatio (k₀ k₁ : Real) : Real :=
  umklappResonanceNumerator k₀ k₁ /
    umklappResonanceDenominator k₀ k₁

theorem umklappResonanceDenominator_ne_zero_of_discriminant_pos
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappResonanceDenominator k₀ k₁ ≠ 0 := by
  intro hzero
  have habs := (umklappTransverseDiscriminant_pos_iff k₀ k₁).1 hdisc
  rw [hzero, abs_zero] at habs
  exact (not_lt_of_ge (abs_nonneg _)) habs

theorem abs_umklappResonanceRatio_lt_one
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    |umklappResonanceRatio k₀ k₁| < 1 := by
  have habs := (umklappTransverseDiscriminant_pos_iff k₀ k₁).1 hdisc
  have hdenominator :=
    umklappResonanceDenominator_ne_zero_of_discriminant_pos hdisc
  have hdenominatorAbs :
      0 < |umklappResonanceDenominator k₀ k₁| :=
    abs_pos.mpr hdenominator
  rw [umklappResonanceRatio, abs_div]
  exact (div_lt_one hdenominatorAbs).2 habs

theorem umklappResonanceRatio_mem_Ioo
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappResonanceRatio k₀ k₁ ∈ Ioo (-1 : Real) 1 :=
  abs_lt.mp (abs_umklappResonanceRatio_lt_one hdisc)

inductive UmklappArcsineBranch
  | principal
  | outer
  deriving DecidableEq

instance : Fintype UmklappArcsineBranch where
  elems := {.principal, .outer}
  complete := by
    intro branch
    cases branch <;> simp

@[simp] theorem card_umklappArcsineBranch :
    Fintype.card UmklappArcsineBranch = 2 := by
  decide

/-- The principal angle and the unique second representative in
`[-pi,pi]`, selected according to the sign of the sine value. -/
def umklappArcsineAngle
    (branch : UmklappArcsineBranch) (ratio : Real) : Real :=
  match branch with
  | .principal => Real.arcsin ratio
  | .outer =>
      if 0 ≤ ratio then
        Real.pi - Real.arcsin ratio
      else
        -Real.pi - Real.arcsin ratio

/-- Convert a moving angle into its free-momentum root. -/
def umklappRootFromAngle (k₀ k₁ angle : Real) : Real :=
  (k₀ + k₁) / 2 + 2 * angle

def umklappArcsineRoot
    (branch : UmklappArcsineBranch) (k₀ k₁ : Real) : Real :=
  umklappRootFromAngle k₀ k₁
    (umklappArcsineAngle branch (umklappResonanceRatio k₀ k₁))

@[simp] theorem umklappMovingAngle_rootFromAngle
    (k₀ k₁ angle : Real) :
    umklappMovingAngle k₀ k₁ (umklappRootFromAngle k₀ k₁ angle) =
      angle := by
  unfold umklappMovingAngle umklappRootFromAngle
  ring

theorem sin_umklappArcsineAngle
    {ratio : Real} (hratio : ratio ∈ Icc (-1 : Real) 1)
    (branch : UmklappArcsineBranch) :
    Real.sin (umklappArcsineAngle branch ratio) = ratio := by
  cases branch
  · exact Real.sin_arcsin hratio.1 hratio.2
  · unfold umklappArcsineAngle
    by_cases hnonnegative : 0 ≤ ratio
    · rw [if_pos hnonnegative, Real.sin_pi_sub,
        Real.sin_arcsin hratio.1 hratio.2]
    · rw [if_neg hnonnegative]
      calc
        Real.sin (-Real.pi - Real.arcsin ratio) =
            Real.sin (Real.arcsin ratio) := by
          rw [show -Real.pi - Real.arcsin ratio =
              -(Real.arcsin ratio + Real.pi) by ring,
            Real.sin_neg, Real.sin_add_pi]
          ring
        _ = ratio := Real.sin_arcsin hratio.1 hratio.2

theorem umklappReducedFourWaveMismatch_eq_ratioEquation
    (k₀ k₁ k₂ : Real) :
    umklappReducedFourWaveMismatch k₀ k₁ k₂ =
      4 * (umklappResonanceNumerator k₀ k₁ -
        umklappResonanceDenominator k₀ k₁ *
          Real.sin (umklappMovingAngle k₀ k₁ k₂)) := by
  rw [umklappReducedFourWaveMismatch_factor]
  rfl

/-- Both explicit arcsine representatives solve the analytic Umklapp
resonance equation whenever the discriminant is positive.  Membership in
the principal Brillouin zone is deliberately checked separately. -/
theorem umklappArcsineRoot_resonant
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (branch : UmklappArcsineBranch) :
    umklappReducedFourWaveMismatch k₀ k₁
      (umklappArcsineRoot branch k₀ k₁) = 0 := by
  have hratio := umklappResonanceRatio_mem_Ioo hdisc
  rw [umklappReducedFourWaveMismatch_eq_ratioEquation,
    umklappArcsineRoot, umklappMovingAngle_rootFromAngle,
    sin_umklappArcsineAngle ⟨hratio.1.le, hratio.2.le⟩ branch]
  have hdenominator :=
    umklappResonanceDenominator_ne_zero_of_discriminant_pos hdisc
  unfold umklappResonanceRatio
  field_simp [hdenominator]
  ring

theorem sin_umklappMovingAngle_eq_resonanceRatio_of_resonant
    {k₀ k₁ k₂ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    Real.sin (umklappMovingAngle k₀ k₁ k₂) =
      umklappResonanceRatio k₀ k₁ := by
  rw [umklappReducedFourWaveMismatch_eq_ratioEquation] at hresonant
  have hrelation :
      umklappResonanceDenominator k₀ k₁ *
          Real.sin (umklappMovingAngle k₀ k₁ k₂) =
        umklappResonanceNumerator k₀ k₁ := by
    nlinarith
  have hdenominator :=
    umklappResonanceDenominator_ne_zero_of_discriminant_pos hdisc
  unfold umklappResonanceRatio
  apply (eq_div_iff hdenominator).2
  simpa [mul_comm] using hrelation

/-- Completeness of the two arcsine representatives on the principal zone:
every positive-discriminant resonant root is either the principal root or
the selected outer root. -/
theorem resonantRoot_eq_principal_or_outer_arcsineRoot
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    k₂ = umklappArcsineRoot .principal k₀ k₁ ∨
      k₂ = umklappArcsineRoot .outer k₀ k₁ := by
  let theta := umklappMovingAngle k₀ k₁ k₂
  let ratio := umklappResonanceRatio k₀ k₁
  have htheta : theta ∈ Ioo (-Real.pi) Real.pi :=
    umklappMovingAngle_mem_Ioo_neg_pi_pi
      hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi
  have hsine : Real.sin theta = ratio := by
    simpa [theta, ratio] using
      sin_umklappMovingAngle_eq_resonanceRatio_of_resonant hdisc hresonant
  have hrootFromAngle :
      k₂ = umklappRootFromAngle k₀ k₁ theta := by
    unfold theta umklappMovingAngle umklappRootFromAngle
    ring
  by_cases hlower : theta < -(Real.pi / 2)
  · have hthetaNeg : theta < 0 := by linarith
    have hsineNeg : Real.sin theta < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hthetaNeg htheta.1
    have hratioNeg : ratio < 0 := by linarith
    let reflected := -Real.pi - theta
    have hreflectedMem : reflected ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [reflected]
      constructor <;> linarith [htheta.1, hlower]
    have hreflectedSine : Real.sin reflected = ratio := by
      calc
        Real.sin reflected = Real.sin theta := by
          dsimp [reflected]
          rw [show -Real.pi - theta = -(theta + Real.pi) by ring,
            Real.sin_neg, Real.sin_add_pi]
          ring
        _ = ratio := hsine
    have harcsin : Real.arcsin ratio = reflected :=
      Real.arcsin_eq_of_sin_eq hreflectedSine hreflectedMem
    right
    calc
      k₂ = umklappRootFromAngle k₀ k₁ theta := hrootFromAngle
      _ = umklappRootFromAngle k₀ k₁
          (umklappArcsineAngle .outer ratio) := by
        congr 1
        simp [umklappArcsineAngle, not_le.mpr hratioNeg,
          harcsin, reflected]
      _ = umklappArcsineRoot .outer k₀ k₁ := by
        rfl
  · by_cases hupper : Real.pi / 2 < theta
    · have hthetaPos : 0 < theta := by linarith
      have hsinePos : 0 < Real.sin theta :=
        Real.sin_pos_of_pos_of_lt_pi hthetaPos htheta.2
      have hratioPos : 0 < ratio := by linarith
      let reflected := Real.pi - theta
      have hreflectedMem : reflected ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        dsimp [reflected]
        constructor <;> linarith [htheta.2, hupper]
      have hreflectedSine : Real.sin reflected = ratio := by
        calc
          Real.sin reflected = Real.sin theta := by
            exact Real.sin_pi_sub theta
          _ = ratio := hsine
      have harcsin : Real.arcsin ratio = reflected :=
        Real.arcsin_eq_of_sin_eq hreflectedSine hreflectedMem
      right
      calc
        k₂ = umklappRootFromAngle k₀ k₁ theta := hrootFromAngle
        _ = umklappRootFromAngle k₀ k₁
            (umklappArcsineAngle .outer ratio) := by
          congr 1
          simp [umklappArcsineAngle, hratioPos.le, harcsin, reflected]
        _ = umklappArcsineRoot .outer k₀ k₁ := by
          rfl
    · have hthetaCentral :
          theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨le_of_not_gt hlower, le_of_not_gt hupper⟩
      have harcsin : Real.arcsin ratio = theta :=
        Real.arcsin_eq_of_sin_eq hsine hthetaCentral
      left
      calc
        k₂ = umklappRootFromAngle k₀ k₁ theta := hrootFromAngle
        _ = umklappRootFromAngle k₀ k₁
            (umklappArcsineAngle .principal ratio) := by
          simp [umklappArcsineAngle, harcsin]
        _ = umklappArcsineRoot .principal k₀ k₁ := by
          rfl

end

end ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
