import Submission.Kakeya
import Family4GlobalExtremalUpstream

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8KatzTaoFrostmanPropertiesV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-!
# Katz--Tao and Frostman multiplicity properties

This file records the two properties in Definitions `def: KKT` and `def: KF`
of the streamlined Wang--Zahl paper.  The normalization is the one used in
the paper: all tubes lie in the unit ball, `delta <= 1/2`, and the constants
in both displayed right-hand sides are exactly one.

There is deliberately no field asserting either property.  These are the
theorem-level predicates which Family 8 must relate.
-/

/-- The closed unit ball, packaged as a convex body for `IsFrostmanIn`. -/
def unitBallBody : ConvexBody Space where
  carrier := Metric.closedBall (0 : Space) 1
  convex' := convex_closedBall (0 : Space) 1
  isCompact' := isCompact_closedBall (0 : Space) 1
  nonempty' := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

@[simp]
theorem coe_unitBallBody :
    (unitBallBody : Set Space) = Metric.closedBall (0 : Space) 1 :=
  rfl

/-- An actual indexed tube family together with the shading used to measure
density and average multiplicity. -/
structure ActualTubeDatum (delta : NNReal) (ι : Type)
    [Fintype ι] [DecidableEq ι] where
  family : UniformTubeFamily delta ι
  shading : Shading family.bodyFamily

namespace ActualTubeDatum

variable {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bounded, essentially-distinct data quantified over in the paper.
The diameter restriction is normalized to `delta <= 1/2`. -/
structure IsAdmissible (D : ActualTubeDatum delta ι) : Prop where
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (2 : NNReal)⁻¹
  contained_in_unit_ball : ∀ i,
    (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1
  pairwise_essentiallyDistinct :
    Set.Pairwise (Set.univ : Set ι) fun i j =>
      EssentiallyDistinct (D.family.tubes i) (D.family.tubes j)

/-- The paper's `|T| |T|`: the indexed sum of actual tube volumes.  Keeping
this quantity rather than replacing it by `card * delta^2` makes the
Frostman right-hand side lossless at this interface. -/
def actualFamilyVolume (D : ActualTubeDatum delta ι) : ENNReal :=
  familyVolume D.family.bodyFamily

end ActualTubeDatum

/-- Exact right-hand side in `K_KT(beta)`: `delta^(-epsilon) #T^beta`. -/
def katzTaoMultiplicityRHS (delta : NNReal) (tubeCount : Nat)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) * (tubeCount : ENNReal) ^ beta

/-- Exact right-hand side in `K_F(beta)`:
`delta^(-epsilon) delta^(-2 beta) (sum_T |T|)^(1-beta/2)`.
The numerical prefactor is exactly one. -/
def frostmanMultiplicityRHS (delta : NNReal) (actualVolume : ENNReal)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    (delta : ENNReal) ^ (-2 * beta) *
      actualVolume ^ (1 - beta / 2)

/-- The two scale-dependent premises in the Katz--Tao property. -/
def KatzTaoHypotheses {delta : NNReal} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (eta : Real) : Prop :=
  (delta : ENNReal) ^ eta ≤ D.shading.shadingDensity ∧
    maximalConcentration D.family.bodyFamily ≤ (delta : ENNReal) ^ (-eta)

/-- The two scale-dependent premises in the Frostman property. -/
def FrostmanHypotheses {delta : NNReal} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (eta : Real) : Prop :=
  (delta : ENNReal) ^ eta ≤ D.shading.shadingDensity ∧
    IsFrostmanIn ((delta : ENNReal) ^ (-eta))
      D.family.bodyFamily unitBallBody

/-- `K_KT(beta)` at fixed `epsilon`, loss exponent `eta`, and terminal scale
`delta0`. -/
def KatzTaoAtParameters (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta : NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
      (D : ActualTubeDatum delta ι),
    D.IsAdmissible →
    delta ≤ delta0 →
    KatzTaoHypotheses D eta →
    D.shading.averageMultiplicity ≤
      katzTaoMultiplicityRHS delta (Fintype.card ι) epsilon beta

/-- `K_F(beta)` at fixed `epsilon`, loss exponent `eta`, and terminal scale
`delta0`. -/
def FrostmanAtParameters (beta epsilon eta : Real) (delta0 : NNReal) : Prop :=
  ∀ (delta : NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
      (D : ActualTubeDatum delta ι),
    D.IsAdmissible →
    delta ≤ delta0 →
    FrostmanHypotheses D eta →
    D.shading.averageMultiplicity ≤
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta

/-- The exact `epsilon -> eta, delta0` quantifiers defining
`K_KT(beta)`. -/
def KatzTaoProperty (beta : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        KatzTaoAtParameters beta epsilon eta delta0

/-- The exact `epsilon -> eta, delta0` quantifiers defining `K_F(beta)`. -/
def FrostmanProperty (beta : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        FrostmanAtParameters beta epsilon eta delta0

/-- The supremal-concentration premise is exactly the existing global
Katz--Tao predicate, including the zero-volume test-body cases. -/
theorem maximalConcentration_le_iff_isKatzTao
    {ι : Type} [Fintype ι] {C : ENNReal} {F : ConvexFamily ι} :
    maximalConcentration F ≤ C ↔ IsKatzTao C F := by
  constructor
  · intro hmax
    apply isKatzTao_iff_concentration_le.mpr
    intro K
    exact (concentration_le_maximalConcentration F K).trans hmax
  · intro hKT
    apply iSup_le
    intro K
    exact (isKatzTao_iff_concentration_le.mp hKT) K

/-- Lossless rewriting of the Katz--Tao premises to the pre-existing
`IsKatzTao` API. -/
theorem katzTaoHypotheses_iff_density_and_isKatzTao
    {delta : NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ActualTubeDatum delta ι) (eta : Real) :
    KatzTaoHypotheses D eta ↔
      (delta : ENNReal) ^ eta ≤ D.shading.shadingDensity ∧
        IsKatzTao ((delta : ENNReal) ^ (-eta)) D.family.bodyFamily := by
  rw [KatzTaoHypotheses, maximalConcentration_le_iff_isKatzTao]

namespace KatzTaoAtParameters

/-- Direct application adapter, exposing all paper hypotheses without a
callback hidden in a structure. -/
theorem apply {beta epsilon eta : Real} {delta0 delta : NNReal}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta ι) (hD : D.IsAdmissible)
    (hdelta : delta ≤ delta0) (hKT : KatzTaoHypotheses D eta) :
    D.shading.averageMultiplicity ≤
      katzTaoMultiplicityRHS delta (Fintype.card ι) epsilon beta :=
  h delta ι D hD hdelta hKT

/-- Shrinking the terminal scale loses nothing. -/
theorem mono_delta0 {beta epsilon eta : Real} {delta0 delta0' : NNReal}
    (h : KatzTaoAtParameters beta epsilon eta delta0)
    (hsmall : delta0' ≤ delta0) :
    KatzTaoAtParameters beta epsilon eta delta0' := by
  intro delta ι _ _ D hD hdelta hKT
  exact h delta ι D hD (hdelta.trans hsmall) hKT

end KatzTaoAtParameters

namespace FrostmanAtParameters

/-- Direct application adapter for the Frostman property. -/
theorem apply {beta epsilon eta : Real} {delta0 delta : NNReal}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta ι) (hD : D.IsAdmissible)
    (hdelta : delta ≤ delta0) (hF : FrostmanHypotheses D eta) :
    D.shading.averageMultiplicity ≤
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta :=
  h delta ι D hD hdelta hF

/-- Shrinking the terminal scale loses nothing. -/
theorem mono_delta0 {beta epsilon eta : Real} {delta0 delta0' : NNReal}
    (h : FrostmanAtParameters beta epsilon eta delta0)
    (hsmall : delta0' ≤ delta0) :
    FrostmanAtParameters beta epsilon eta delta0' := by
  intro delta ι _ _ D hD hdelta hF
  exact h delta ι D hD (hdelta.trans hsmall) hF

end FrostmanAtParameters

/-- Unpack the defining Katz--Tao quantifiers. -/
theorem KatzTaoProperty.exists_parameters {beta epsilon : Real}
    (h : KatzTaoProperty beta) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        KatzTaoAtParameters beta epsilon eta delta0 :=
  h epsilon hepsilon

/-- Unpack the defining Frostman quantifiers. -/
theorem FrostmanProperty.exists_parameters {beta epsilon : Real}
    (h : FrostmanProperty beta) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
        FrostmanAtParameters beta epsilon eta delta0 :=
  h epsilon hepsilon

#print axioms coe_unitBallBody
#print axioms maximalConcentration_le_iff_isKatzTao
#print axioms katzTaoHypotheses_iff_density_and_isKatzTao
#print axioms KatzTaoAtParameters.apply
#print axioms KatzTaoAtParameters.mono_delta0
#print axioms FrostmanAtParameters.apply
#print axioms FrostmanAtParameters.mono_delta0
#print axioms KatzTaoProperty.exists_parameters
#print axioms FrostmanProperty.exists_parameters

end

end Family8KatzTaoFrostmanPropertiesV1
