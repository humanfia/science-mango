import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

/-!
# Fiber covering growth from multiplicity and set growth

This module isolates the first missing geometric-to-algebraic bridge for
induced-shading density.  A genuine pointwise bound for the multiplicity in
each active fine fiber is integrated over that fiber's actual shaded union.
The resulting mass bound is then composed with one explicit set-level
cross-multiplied growth estimate into the actual neighborhood-induced carrier.

The set-level estimate is intentionally the only remaining geometric input:
in applications it must account for the passage from a full thickening to its
intersection with the coarse body.  `HasFiberCoveringGrowth` itself is a
derived conclusion, never an input below.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FiberwiseMultiplicityAssembly
open FactoringMultiplicityAssembly
open InducedShadingDensityAlgebra

noncomputable section

namespace FiberCoveringGrowthFromMultiplicity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- Pointwise fiber multiplicity is uniformly bounded on every active fiber's
actual shaded union.  Outside that union the multiplicity vanishes. -/
def HasActiveFiberMultiplicityBound
    (P : ConvexFactorization F W) (Y : Shading F) (m : ℕ) : Prop :=
  ∀ k ∈ P.index.coarse, ∀ x ∈ P.fiberShadedUnion Y k,
    P.fiberMultiplicity Y k x ≤ m

/-- The remaining set-level geometric input.  It directly targets the actual
coarse-body-intersected neighborhood carrier, so no hidden
full-thickening-to-intersection comparison is used. -/
def HasFiberSetGrowth
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : ℝ) (scale growth : ℝ≥0∞) : Prop :=
  ∀ k ∈ P.index.coarse,
    volume (P.fiberShadedUnion Y k) * scale ≤
      growth * volume ((P.neighborhoodInducedShading Y r).carrier k)

/-- Restricting a shading to one fiber has exactly the paper-style fiber
shaded union. -/
theorem fiberShading_shadedUnion_eq_fiberShadedUnion
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    (fiberShading P Y k).shadedUnion = P.fiberShadedUnion Y k := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [fiberShading_carrier] at hxi
    by_cases hi : i ∈ P.index.fiber k
    · exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, by simpa [hi] using hxi⟩
    · simp [hi] at hxi
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr
      ⟨i.1, by simpa [fiberShading_carrier, i.2] using hxi⟩

/-- The density bridge's fiber mass is the shading mass of the genuine
single-fiber restriction. -/
theorem fiberShadingMass_eq_fiberShading_mass
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    fiberShadingMass P Y k = (fiberShading P Y k).shadingMass := by
  simpa [fiberShadingMass] using
    (fiberShading_mass_eq_sum_fiber P Y k).symm

/-- A pointwise multiplicity bound on the actual fiber union integrates to
the desired multiplicity-counted fiber-mass bound. -/
theorem fiberShadingMass_le_nsmul_volume_fiberShadedUnion
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (m : ℕ)
    (hpoint : ∀ x ∈ P.fiberShadedUnion Y k,
      P.fiberMultiplicity Y k x ≤ m) :
    fiberShadingMass P Y k ≤
      m • volume (P.fiberShadedUnion Y k) := by
  rw [fiberShadingMass_eq_fiberShading_mass,
    ← fiberShading_shadedUnion_eq_fiberShadedUnion]
  apply FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
  intro x
  rw [fiberShading_pointMultiplicity]
  by_cases hx : x ∈ P.fiberShadedUnion Y k
  · exact hpoint x hx
  · have hx' : x ∉ (fiberShading P Y k).shadedUnion := by
      rwa [fiberShading_shadedUnion_eq_fiberShadedUnion]
    have hzero : (fiberShading P Y k).pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx' ((fiberShading P Y k).pointMultiplicity_pos_iff_mem_shadedUnion x |>.1 hpos)
    rw [fiberShading_pointMultiplicity] at hzero
    simp [hzero]

/-- The multiplicity mass estimate composes with one set-level cross growth
estimate, with no division and hence no zero- or infinity-side conditions. -/
theorem fiberShadingMass_mul_scale_le_of_multiplicity_of_setGrowth
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (m : ℕ)
    (r : ℝ) (scale growth : ℝ≥0∞)
    (hpoint : ∀ x ∈ P.fiberShadedUnion Y k,
      P.fiberMultiplicity Y k x ≤ m)
    (hset : volume (P.fiberShadedUnion Y k) * scale ≤
      growth * volume ((P.neighborhoodInducedShading Y r).carrier k)) :
    fiberShadingMass P Y k * scale ≤
      ((m : ℝ≥0∞) * growth) *
        volume ((P.neighborhoodInducedShading Y r).carrier k) := by
  have hmass :=
    fiberShadingMass_le_nsmul_volume_fiberShadedUnion P Y k m hpoint
  calc
    fiberShadingMass P Y k * scale ≤
        (m • volume (P.fiberShadedUnion Y k)) * scale :=
      mul_le_mul' hmass le_rfl
    _ = (m : ℝ≥0∞) *
        (volume (P.fiberShadedUnion Y k) * scale) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ (m : ℝ≥0∞) *
        (growth * volume ((P.neighborhoodInducedShading Y r).carrier k)) :=
      mul_le_mul' le_rfl hset
    _ = ((m : ℝ≥0∞) * growth) *
        volume ((P.neighborhoodInducedShading Y r).carrier k) := by
      ac_rfl

/-- Uniform active-fiber pointwise control and genuine set growth produce the
`HasFiberCoveringGrowth` input consumed by the induced-density algebra. -/
theorem hasFiberCoveringGrowth_of_multiplicity_of_setGrowth
    (P : ConvexFactorization F W) (Y : Shading F) (m : ℕ)
    (r : ℝ) (scale growth : ℝ≥0∞)
    (hmult : HasActiveFiberMultiplicityBound P Y m)
    (hset : HasFiberSetGrowth P Y r scale growth) :
    HasFiberCoveringGrowth P Y r scale ((m : ℝ≥0∞) * growth) := by
  intro k hk
  exact fiberShadingMass_mul_scale_le_of_multiplicity_of_setGrowth
    P Y k m r scale growth (hmult k hk) (hset k hk)

/-- An actual exact factoring assembly supplies the required active-fiber
multiplicity bound at its selected fine level. -/
theorem exactAssembly_hasActiveFiberMultiplicityBound
    {P : ConvexFactorization F W} {Y : Shading F} {loss : ℕ}
    (A : ExactAssembly P Y loss) :
    HasActiveFiberMultiplicityBound
      P A.refinement.shading A.fineLevel := by
  intro k hk x _hx
  exact A.fiberMultiplicity_refinement_le_fineLevel k hk x

/-- Consequently, set-level growth for the refined shading of a genuine
assembly yields its full fiber covering-growth certificate. -/
theorem exactAssembly_hasFiberCoveringGrowth_of_setGrowth
    {P : ConvexFactorization F W} {Y : Shading F} {loss : ℕ}
    (A : ExactAssembly P Y loss)
    (r : ℝ) (scale growth : ℝ≥0∞)
    (hset : HasFiberSetGrowth
      P A.refinement.shading r scale growth) :
    HasFiberCoveringGrowth P A.refinement.shading r scale
      ((A.fineLevel : ℝ≥0∞) * growth) :=
  hasFiberCoveringGrowth_of_multiplicity_of_setGrowth
    P A.refinement.shading A.fineLevel r scale growth
      (exactAssembly_hasActiveFiberMultiplicityBound A) hset

end FiberCoveringGrowthFromMultiplicity

end

end Submission.Kakeya.ConvexFactoring
