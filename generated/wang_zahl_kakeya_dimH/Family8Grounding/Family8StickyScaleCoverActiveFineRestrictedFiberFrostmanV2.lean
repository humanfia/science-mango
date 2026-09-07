import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3

/-!
# Frostman transport to fully active restricted fibres, V2

V1 omitted the direct owner/open of `restrictedCoarseEquivActive` and is
frozen.  This clean successor keeps the body-preserving equivalence argument
unchanged and makes that dependency explicit.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedFiberFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictedParentTransportV2.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- `IsFrostmanIn` is unchanged when a finite family is reindexed through an
equivalence that preserves every body literally. -/
theorem isFrostmanIn_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a))
    {C : ENNReal} {K : ConvexBody Space}
    (h : IsFrostmanIn C F K) : IsFrostmanIn C G K := by
  refine ⟨?_, ?_⟩
  · intro b
    have hb := hbody (e.symm b)
    rw [e.apply_symm_apply] at hb
    rw [← hb]
    exact h.1 (e.symm b)
  · intro K' hK'
    simpa only [
      containedMass_eq_of_bodyPreservingEquiv e F G hbody K',
      containedMass_eq_of_bodyPreservingEquiv e F G hbody K] using
        h.2 K' hK'

theorem isFrostmanIn_iff_of_bodyPreservingEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (hbody : ∀ a, F a = G (e a))
    {C : ENNReal} {K : ConvexBody Space} :
    IsFrostmanIn C F K ↔ IsFrostmanIn C G K := by
  constructor
  · exact isFrostmanIn_of_bodyPreservingEquiv e F G hbody
  · apply isFrostmanIn_of_bodyPreservingEquiv e.symm G F
    intro b
    have hb := hbody (e.symm b)
    simpa only [e.apply_symm_apply] using hb.symm

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The Frostman certificate on an original active fibre transports exactly
to the corresponding fibre of the fully active restricted cover. -/
theorem activeFineRestricted_fiber_isFrostmanOn
    (S : StickyScaleCover fine rho)
    (q : Fin (activeFineRestrictedScaleCover S).coarseCard)
    {C : ENNReal} (K : ConvexBody Space)
    (h : IsFrostmanOn C fine.bodyFamily
      (S.fiber (restrictedCoarseEquivActive S q).1) K) :
    IsFrostmanOn C (activeFineRestrictedFamily S).bodyFamily
      ((activeFineRestrictedScaleCover S).fiber q) K := by
  have hOriginal : IsFrostmanIn C
      (S.fiberFamily (restrictedCoarseEquivActive S q).1) K :=
    (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily
      (S.fiber (restrictedCoarseEquivActive S q).1) K).mp h
  have hRestricted : IsFrostmanIn C
      ((activeFineRestrictedScaleCover S).fiberFamily q) K :=
    (isFrostmanIn_iff_of_bodyPreservingEquiv
      (activeFineRestrictedFiberEquiv S q)
      ((activeFineRestrictedScaleCover S).fiberFamily q)
      (S.fiberFamily (restrictedCoarseEquivActive S q).1)
      (activeFineRestrictedFiberEquiv_body S q)).mpr hOriginal
  exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    (activeFineRestrictedFamily S).bodyFamily
    ((activeFineRestrictedScaleCover S).fiber q) K).mpr hRestricted

#print axioms isFrostmanIn_of_bodyPreservingEquiv
#print axioms isFrostmanIn_iff_of_bodyPreservingEquiv
#print axioms activeFineRestricted_fiber_isFrostmanOn

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedFiberFrostmanV2
