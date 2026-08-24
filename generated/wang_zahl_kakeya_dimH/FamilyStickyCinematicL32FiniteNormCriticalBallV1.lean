import FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32FiniteNormCriticalBallV1

open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

noncomputable section

/-!
# The local norm critical ball from the exact finite maximizer

This is the first, pointwise step in the order used in PYZ Section 5.1.1.
The selected scale and centre are the two components of the same exact
weighted-score maximizer.  The ball is the literal filter of the source
family.  Its weighted cardinal retention and its metric diameter are proved
here; neither is stored as an input field.
-/

variable {alpha : Type*}

/-- The literal closed critical ball `B_x` inside a finite family. -/
noncomputable def finiteNormCriticalBall
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) :
    Finset alpha :=
  family.filter fun f =>
    distance f
        (finiteCriticalMaximizerCenter family distance delta ceiling exponent
          hfamily) ≤
      finiteCriticalMaximizerScale family distance delta ceiling exponent
        hfamily

/-- The cardinality of the literal filter is the finite ball count used in
the weighted score. -/
theorem finiteNormCriticalBall_card
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) :
    (finiteNormCriticalBall family distance delta ceiling exponent
      hfamily).card =
      finiteBallCount family distance
        (finiteCriticalMaximizerScale family distance delta ceiling exponent
          hfamily)
        (finiteCriticalMaximizerCenter family distance delta ceiling exponent
          hfamily) := by
  rfl

/-- The critical ball is a literal subfamily. -/
theorem finiteNormCriticalBall_subset
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty) :
    finiteNormCriticalBall family distance delta ceiling exponent hfamily ⊆
      family := by
  exact Finset.filter_subset _ _

/-- A ball at a radius containing every family member has full cardinality. -/
theorem finiteBallCount_eq_card_of_forall_le
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (radius : Real) (center : alpha)
    (hfull : ∀ f, f ∈ family → distance f center ≤ radius) :
    finiteBallCount family distance radius center = family.card := by
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]
  constructor
  · exact fun hf => hf.1
  · exact fun hf => ⟨hf, hfull f hf⟩

/-- The selected centre belongs to its own critical ball. -/
theorem finiteCriticalMaximizerCenter_mem_finiteNormCriticalBall
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent : Real} (hfamily : family.Nonempty)
    (hself : ∀ center, center ∈ family →
      distance center center ≤ delta)
    (hdeltaCeiling : delta ≤ ceiling) :
    finiteCriticalMaximizerCenter family distance delta ceiling exponent
        hfamily ∈
      finiteNormCriticalBall family distance delta ceiling exponent
        hfamily := by
  rw [finiteNormCriticalBall, Finset.mem_filter]
  refine ⟨finiteCriticalMaximizerCenter_mem family distance delta ceiling
    exponent hfamily, ?_⟩
  exact (hself _ (finiteCriticalMaximizerCenter_mem family distance delta
    ceiling exponent hfamily)).trans
      (finiteCriticalMaximizerScale_bounds family distance hfamily
        hdeltaCeiling).1

/-- In particular, the local critical ball is nonempty. -/
theorem finiteNormCriticalBall_nonempty
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent : Real} (hfamily : family.Nonempty)
    (hself : ∀ center, center ∈ family →
      distance center center ≤ delta)
    (hdeltaCeiling : delta ≤ ceiling) :
    (finiteNormCriticalBall family distance delta ceiling exponent
      hfamily).Nonempty :=
  ⟨_, finiteCriticalMaximizerCenter_mem_finiteNormCriticalBall
    family distance hfamily hself hdeltaCeiling⟩

/-- Exact weighted-cardinality retention against any full comparison ball at
the ceiling scale.  This is the finite form of the inequality defining
`n₂(x)` in PYZ; it follows from maximizer domination. -/
theorem finiteNormCriticalBall_weighted_card_retention
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent : Real} (hfamily : family.Nonempty)
    (hself : ∀ center, center ∈ family →
      distance center center ≤ delta)
    (hdelta : 0 < delta) (hdeltaCeiling : delta ≤ ceiling)
    (hexponent : 0 ≤ exponent)
    (testCenter : alpha) (htestCenter : testCenter ∈ family)
    (hfull : ∀ f, f ∈ family → distance f testCenter ≤ ceiling) :
    (family.card : Real) * ceiling ^ (-exponent) ≤
      ((finiteNormCriticalBall family distance delta ceiling exponent
        hfamily).card : Real) *
        (finiteCriticalMaximizerScale family distance delta ceiling exponent
          hfamily) ^ (-exponent) := by
  have hdom := canonicalCriticalMaximizer_dominates_on_Icc
    family distance hfamily hself hdelta hdeltaCeiling hexponent
    ceiling hdeltaCeiling le_rfl testCenter htestCenter
  have hcount := finiteBallCount_eq_card_of_forall_le
    family distance ceiling testCenter hfull
  simpa only [finiteTwoEndsScore, hcount, finiteNormCriticalBall_card,
    finiteCriticalMaximizerScale, finiteCriticalMaximizerCenter] using hdom

/-- Triangle inequality and symmetry give the honest diameter `2 t(x)` of
the local critical ball. -/
theorem finiteNormCriticalBall_distance_le_two_scale
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty)
    (hsymm : ∀ f g, distance f g = distance g f)
    (htriangle : ∀ f center g,
      distance f g ≤ distance f center + distance center g)
    {f g : alpha}
    (hf : f ∈ finiteNormCriticalBall family distance delta ceiling
      exponent hfamily)
    (hg : g ∈ finiteNormCriticalBall family distance delta ceiling
      exponent hfamily) :
    distance f g ≤
      2 * finiteCriticalMaximizerScale family distance delta ceiling
        exponent hfamily := by
  have hfBall := (Finset.mem_filter.mp hf).2
  have hgBall := (Finset.mem_filter.mp hg).2
  calc
    distance f g ≤
        distance f (finiteCriticalMaximizerCenter family distance delta
          ceiling exponent hfamily) +
        distance (finiteCriticalMaximizerCenter family distance delta
          ceiling exponent hfamily) g :=
      htriangle _ _ _
    _ = distance f (finiteCriticalMaximizerCenter family distance delta
          ceiling exponent hfamily) +
        distance g (finiteCriticalMaximizerCenter family distance delta
          ceiling exponent hfamily) := by
      rw [hsymm
        (finiteCriticalMaximizerCenter family distance delta ceiling exponent
          hfamily) g]
    _ ≤ finiteCriticalMaximizerScale family distance delta ceiling exponent
          hfamily +
        finiteCriticalMaximizerScale family distance delta ceiling exponent
          hfamily := add_le_add hfBall hgBall
    _ = 2 * finiteCriticalMaximizerScale family distance delta ceiling
          exponent hfamily := by rw [two_mul]

#print axioms finiteNormCriticalBall
#print axioms finiteNormCriticalBall_card
#print axioms finiteNormCriticalBall_subset
#print axioms finiteBallCount_eq_card_of_forall_le
#print axioms finiteCriticalMaximizerCenter_mem_finiteNormCriticalBall
#print axioms finiteNormCriticalBall_nonempty
#print axioms finiteNormCriticalBall_weighted_card_retention
#print axioms finiteNormCriticalBall_distance_le_two_scale

end

end FamilyStickyCinematicL32FiniteNormCriticalBallV1
