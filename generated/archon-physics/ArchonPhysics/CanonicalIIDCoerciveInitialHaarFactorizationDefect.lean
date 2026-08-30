import ArchonPhysics.CanonicalIIDCoerciveInitialHaarAnnealedFactorization
import ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure

/-!
# Exact initial factorization defect: Haar selector times mass covariance

For two disjoint finite index blocks, disjoint aggregate phase-charge
supports prevent phase cancellation between the blocks.  Under that precise
condition the actual canonical continuous-law factorization defect at time
zero is

    left Haar selector * right Haar selector * radial mass covariance.

Thus the defect vanishes if either block is charge-unbalanced.  When both
blocks are balanced it is exactly the covariance caused by the common random
mass configuration, and vanishes only with an additional radial-factorization
input.  A physically transparent sufficient premise -- no ordered phase mode
appears in both blocks -- is also supplied.

This is the strongest unconditional Haar conclusion available for the actual
annealed amplitudes.  It does not replace the surviving balanced mass
covariance by independence and makes no positive-time claim.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarAnnealedFactorization
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Set of ordered phase modes occurring in a finite index block. -/
def canonicalOrderedBlockModeSupport
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) : Set (Lattice.Site N) :=
  {mode | ∃ i ∈ block,
    (canonicalOrderedSignedMode (N := N) (entry i)).mode = mode}

/-- The support of the aggregate phase charge is contained in the set of
ordered modes occurring in the block. -/
theorem support_canonicalOrderedSignedBlockCharge_subset_modeSupport
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry block) ⊆
      canonicalOrderedBlockModeSupport (N := N) entry block := by
  intro mode hmode
  change canonicalOrderedSignedBlockCharge (N := N) entry block mode ≠ 0
    at hmode
  change ∃ i ∈ block,
    (canonicalOrderedSignedMode (N := N) (entry i)).mode = mode
  by_contra hnone
  push Not at hnone
  apply hmode
  simp only [canonicalOrderedSignedBlockCharge, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp [SignedMode.charge, Pi.single_apply, hnone i hi]

/-- Aggregate ordered-mode charges add over disjoint index blocks. -/
theorem canonicalOrderedSignedBlockCharge_union
    (entry : I → PhaseSign × OrderedModeIndex N)
    {left right : Finset I} (hindex : Disjoint left right) :
    canonicalOrderedSignedBlockCharge (N := N) entry (left ∪ right) =
      canonicalOrderedSignedBlockCharge (N := N) entry left +
        canonicalOrderedSignedBlockCharge (N := N) entry right := by
  unfold canonicalOrderedSignedBlockCharge
  rw [Finset.sum_union hindex]

/-- The mass-only remainder left by two initially phase-separated blocks. -/
def canonicalInitialRadialBlockCovariance
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) : Complex :=
  canonicalInitialRadialBlockMean (N := N) a entry (left ∪ right) -
    canonicalInitialRadialBlockMean (N := N) a entry left *
      canonicalInitialRadialBlockMean (N := N) a entry right

/-- Exact actual canonical time-zero factorization defect.  The only
surviving phase-separated sector is balanced--balanced, where the complete
random-mass radial covariance is retained. -/
theorem canonicalCoerciveClusterFactorizationDefect_zero_eq_selectors_mul_covariance
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right))) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right 0 =
      (if canonicalOrderedSignedBlockCharge (N := N) entry left = 0
          then (1 : Complex) else 0) *
        (if canonicalOrderedSignedBlockCharge (N := N) entry right = 0
          then (1 : Complex) else 0) *
        canonicalInitialRadialBlockCovariance (N := N)
          a entry left right := by
  let leftCharge :=
    canonicalOrderedSignedBlockCharge (N := N) entry left
  let rightCharge :=
    canonicalOrderedSignedBlockCharge (N := N) entry right
  have hunion :
      canonicalOrderedSignedBlockCharge (N := N) entry (left ∪ right) =
        leftCharge + rightCharge := by
    exact canonicalOrderedSignedBlockCharge_union entry hindex
  unfold canonicalCoerciveClusterFactorizationDefect
    blockFactorizationDefect
  rw [
    canonicalSignedBlockBochnerIntegral_zero_eq_radialMean_mul_selector
      hN ha0 ha1 kappa beta g hbeta entry hpositive (left ∪ right),
    canonicalSignedBlockBochnerIntegral_zero_eq_radialMean_mul_selector
      hN ha0 ha1 kappa beta g hbeta entry hpositive left,
    canonicalSignedBlockBochnerIntegral_zero_eq_radialMean_mul_selector
      hN ha0 ha1 kappa beta g hbeta entry hpositive right,
    hunion]
  unfold canonicalInitialRadialBlockCovariance
  by_cases hleft : leftCharge = 0
  · by_cases hright : rightCharge = 0
    · simp [leftCharge, rightCharge, hleft, hright]
    · simp [leftCharge, rightCharge, hleft, hright]
  · by_cases hright : rightCharge = 0
    · simp [leftCharge, rightCharge, hleft, hright]
    · have hadd : leftCharge + rightCharge ≠ 0 :=
        add_ne_zero_of_left_ne_zero_of_disjoint_support
          leftCharge rightCharge hleft hcharge
      simp [leftCharge, rightCharge, hleft, hright, hadd]

/-- Exact zero defect whenever the left phase-separated block is
charge-unbalanced. -/
theorem canonicalCoerciveClusterFactorizationDefect_zero_eq_zero_of_leftCharge
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)))
    (hleft : canonicalOrderedSignedBlockCharge (N := N) entry left ≠ 0) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right 0 = 0 := by
  rw [canonicalCoerciveClusterFactorizationDefect_zero_eq_selectors_mul_covariance
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex hcharge]
  simp [hleft]

/-- Exact zero defect whenever the right phase-separated block is
charge-unbalanced. -/
theorem canonicalCoerciveClusterFactorizationDefect_zero_eq_zero_of_rightCharge
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)))
    (hright : canonicalOrderedSignedBlockCharge (N := N) entry right ≠ 0) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right 0 = 0 := by
  rw [canonicalCoerciveClusterFactorizationDefect_zero_eq_selectors_mul_covariance
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex hcharge]
  simp [hright]

/-- In the balanced--balanced sector the defect is exactly the random-mass
radial covariance. -/
theorem canonicalCoerciveClusterFactorizationDefect_zero_eq_covariance_of_balanced
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)))
    (hleft : canonicalOrderedSignedBlockCharge (N := N) entry left = 0)
    (hright : canonicalOrderedSignedBlockCharge (N := N) entry right = 0) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right 0 =
      canonicalInitialRadialBlockCovariance (N := N)
        a entry left right := by
  rw [canonicalCoerciveClusterFactorizationDefect_zero_eq_selectors_mul_covariance
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex hcharge]
  simp [hleft, hright]

/-- Full initial factorization follows if the remaining random-mass radial
mean is supplied to factorize.  This extra statement is not inferred from
Haar phase independence. -/
theorem canonicalCoerciveClusterFactorizationDefect_zero_eq_zero_of_radialFactorization
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)))
    (hmass :
      canonicalInitialRadialBlockMean (N := N) a entry (left ∪ right) =
        canonicalInitialRadialBlockMean (N := N) a entry left *
          canonicalInitialRadialBlockMean (N := N) a entry right) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right 0 = 0 := by
  rw [canonicalCoerciveClusterFactorizationDefect_zero_eq_selectors_mul_covariance
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex hcharge]
  simp [canonicalInitialRadialBlockCovariance, hmass]

/-- Disjoint ordered-mode clusters imply the aggregate charge-support
premise used above. -/
theorem disjoint_chargeSupport_of_disjoint_orderedModeClusters
    (entry : I → PhaseSign × OrderedModeIndex N)
    {left right : Finset I}
    (hcluster : Disjoint
      (canonicalOrderedBlockModeSupport (N := N) entry left)
      (canonicalOrderedBlockModeSupport (N := N) entry right)) :
    Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right)) :=
  hcluster.mono
    (support_canonicalOrderedSignedBlockCharge_subset_modeSupport entry left)
    (support_canonicalOrderedSignedBlockCharge_subset_modeSupport entry right)

end

end ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect
