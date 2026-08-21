import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Submission.Kakeya.ConvexFactoring.NonConcentration
import Submission.Kakeya.Uniformity.TubeFamily

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family6PlankKatzTaoFrostmanActualAdaptersV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring

noncomputable section

universe u

/-- The former tube-shaped Katz--Tao factor, restated locally so this stable
core does not import the vanished scratch dependency chain of the old
adapter. -/
def tubeKatzTaoFactor
    (delta : NNReal) (iota : Type u) [Fintype iota]
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    (Fintype.card iota : ENNReal) ^ beta

/-- The former tube-shaped Frostman factor, restated locally. -/
def tubeFrostmanFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (T : UniformTubeFamily delta iota)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    (delta : ENNReal) ^ (-2 * beta) *
    (familyVolume T.bodyFamily) ^ (1 - beta / 2)

/-- The Katz--Tao factor for an actual uniformly `a x b x 1` plank family.
The analytic small scale is its shortest side `a`; the middle side `b` is
recorded by the geometric certificate below rather than erased by a tube
reboxing. -/
def actualKatzTaoPlankFactor
    (a : NNReal) (iota : Type u) [Fintype iota]
    (epsilon beta : Real) : ENNReal :=
  (a : ENNReal) ^ (-epsilon) *
    (Fintype.card iota : ENNReal) ^ beta

/-- The Frostman factor for an actual uniformly `a x b x 1` plank family.
Using the actual `familyVolume` retains the anisotropic middle-side volume. -/
def actualFrostmanPlankFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    (a : NNReal) (G : ConvexFamily iota)
    (epsilon beta : Real) : ENNReal :=
  (a : ENNReal) ^ (-epsilon) *
    (a : ENNReal) ^ (-2 * beta) *
    (familyVolume G) ^ (1 - beta / 2)

/-- Stable project-core form of the equivalence used to turn an actual
`IsKatzTao` certificate into the maximal-concentration premise. -/
theorem isKatzTao_iff_maximalConcentration_le
    {iota : Type u} [Fintype iota]
    {G : ConvexFamily iota} {K : ENNReal} :
    IsKatzTao K G <-> maximalConcentration G <= K := by
  constructor
  · intro hKT
    apply iSup_le
    intro body
    exact (isKatzTao_iff_concentration_le.mp hKT) body
  · intro hmax
    apply isKatzTao_iff_concentration_le.mpr
    intro body
    exact (concentration_le_maximalConcentration G body).trans hmax

/-- The actual-family Katz--Tao hypothesis on uniformly comparable planks.
Unlike the former tube-only interface, this accepts an arbitrary
`iota -> ConvexBody` together with one common `IsPlank C a b` certificate.
This is the geometric domain produced by per-parent anisotropic
normalization. -/
structure ActualPlankKatzTaoMultiplicityHypothesis
    (UniverseMarker : Type u) (beta : Real) : Prop where
  bound :
    forall epsilon : Real, 0 < epsilon ->
      exists eta : Real, exists a0 : NNReal,
        0 < eta /\ 0 < a0 /\
        forall (a b C : NNReal) (iota : Type u)
          [Fintype iota] [DecidableEq iota]
          (G : ConvexFamily iota) (Z : Shading G),
          0 < a ->
          a <= a0 ->
          (forall i, IsPlank C a b (G i)) ->
          maximalConcentration G <= (a : ENNReal) ^ (-eta) ->
          (a : ENNReal) ^ eta <= Z.shadingDensity ->
          Z.averageMultiplicity <=
            actualKatzTaoPlankFactor a iota epsilon beta

/-- The actual-family Frostman hypothesis on uniformly comparable planks.
Its conclusion uses the true family volume, so no equal-volume or
tube-reboxing premise is hidden in the interface. -/
structure ActualPlankFrostmanMultiplicityHypothesis
    (UniverseMarker : Type u) (beta : Real) : Prop where
  bound :
    forall epsilon : Real, 0 < epsilon ->
      exists eta : Real, exists a0 : NNReal,
        0 < eta /\ 0 < a0 /\
        forall (a b C : NNReal) (iota : Type u)
          [Fintype iota] [DecidableEq iota]
          (G : ConvexFamily iota) (Z : Shading G)
          (ambient : ConvexBody Space) (CF : ENNReal),
          0 < a ->
          a <= a0 ->
          (forall i, IsPlank C a b (G i)) ->
          IsFrostmanIn CF G ambient ->
          CF <= (a : ENNReal) ^ (-eta) ->
          (a : ENNReal) ^ eta <= Z.shadingDensity ->
          Z.averageMultiplicity <=
            actualFrostmanPlankFactor a G epsilon beta

/-- A uniformly certified tube body family is a special case of the plank
Katz--Tao hypothesis.  The certificate is explicit because a metric
thickening of a unit segment is not definitionally an `a x a x 1` plank. -/
theorem ActualPlankKatzTaoMultiplicityHypothesis.uniformTube_bound_of_isPlank
    {UniverseMarker : Type u} {beta : Real}
    (H : ActualPlankKatzTaoMultiplicityHypothesis UniverseMarker beta)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists eta : Real, exists a0 : NNReal,
      0 < eta /\ 0 < a0 /\
      forall (a b C : NNReal) (iota : Type u)
        [Fintype iota] [DecidableEq iota]
        (T : UniformTubeFamily a iota) (Z : Shading T.bodyFamily),
        0 < a ->
        a <= a0 ->
        (forall i, IsPlank C a b (T.bodyFamily i)) ->
        maximalConcentration T.bodyFamily <= (a : ENNReal) ^ (-eta) ->
        (a : ENNReal) ^ eta <= Z.shadingDensity ->
        Z.averageMultiplicity <=
          tubeKatzTaoFactor a iota epsilon beta := by
  rcases H.bound epsilon hepsilon with
    ⟨eta, a0, heta, ha0, hbound⟩
  refine ⟨eta, a0, heta, ha0, ?_⟩
  intro a b C iota _ _ T Z ha ha0' hplank hmax hdensity
  simpa [actualKatzTaoPlankFactor, tubeKatzTaoFactor] using
    hbound a b C iota T.bodyFamily Z ha ha0' hplank hmax hdensity

/-- Frostman tube specialization of the plank hypothesis, conditional only
on the honest uniform plank certificate for the bodies being supplied. -/
theorem ActualPlankFrostmanMultiplicityHypothesis.uniformTube_bound_of_isPlank
    {UniverseMarker : Type u} {beta : Real}
    (H : ActualPlankFrostmanMultiplicityHypothesis UniverseMarker beta)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists eta : Real, exists a0 : NNReal,
      0 < eta /\ 0 < a0 /\
      forall (a b C : NNReal) (iota : Type u)
        [Fintype iota] [DecidableEq iota]
        (T : UniformTubeFamily a iota) (Z : Shading T.bodyFamily)
        (ambient : ConvexBody Space) (CF : ENNReal),
        0 < a ->
        a <= a0 ->
        (forall i, IsPlank C a b (T.bodyFamily i)) ->
        IsFrostmanIn CF T.bodyFamily ambient ->
        CF <= (a : ENNReal) ^ (-eta) ->
        (a : ENNReal) ^ eta <= Z.shadingDensity ->
        Z.averageMultiplicity <=
          tubeFrostmanFactor T epsilon beta := by
  rcases H.bound epsilon hepsilon with
    ⟨eta, a0, heta, ha0, hbound⟩
  refine ⟨eta, a0, heta, ha0, ?_⟩
  intro a b C iota _ _ T Z ambient CF ha ha0' hplank hF hCF hdensity
  simpa [actualFrostmanPlankFactor, tubeFrostmanFactor] using
    hbound a b C iota T.bodyFamily Z ambient CF ha ha0' hplank hF hCF
      hdensity

#print axioms ActualPlankKatzTaoMultiplicityHypothesis.uniformTube_bound_of_isPlank
#print axioms ActualPlankFrostmanMultiplicityHypothesis.uniformTube_bound_of_isPlank

end
end Family6PlankKatzTaoFrostmanActualAdaptersV1
