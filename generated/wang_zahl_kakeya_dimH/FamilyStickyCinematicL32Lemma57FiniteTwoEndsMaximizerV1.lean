import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod

set_option autoImplicit false

namespace FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1

noncomputable section

/-!
# A finite two-ends maximizer for PYZ Lemma 5.7

The source defines `n₂(x)` as a supremum of weighted ball counts and then
chooses a radius and center that approximately attain it.  On finite scale
and center carriers the maximizer is attained exactly.  This module produces
that maximizing pair and its universal weighted-ball domination directly;
no ball-count estimate is assumed as a callback.
-/

variable {alpha : Type*}

/-- Cardinality of the part of `family` in the closed scalar ball around
`center`.  The scalar distance is abstract to cover the C² norm and the
concrete coefficient distance facade. -/
def finiteBallCount (family : Finset alpha)
    (distance : alpha -> alpha -> Real) (radius : Real) (center : alpha) : Nat :=
  (family.filter fun f => distance f center <= radius).card

/-- Weighted ball count used by the finite two-ends maximization. -/
def finiteTwoEndsScore (family : Finset alpha)
    (distance : alpha -> alpha -> Real) (exponent radius : Real)
    (center : alpha) : Real :=
  finiteBallCount family distance radius center * radius ^ (-exponent)

/-- A nonempty finite scale carrier and nonempty finite center carrier have
an exactly maximizing weighted ball. -/
theorem exists_finiteTwoEndsScore_maximizer
    (family centers : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real)
    (hscales : scales.Nonempty) (hcenters : centers.Nonempty) :
    exists chosenScale, chosenScale ∈ scales ∧
      exists chosenCenter, chosenCenter ∈ centers ∧
        forall radius, radius ∈ scales -> forall center, center ∈ centers ->
          finiteTwoEndsScore family distance exponent radius center <=
            finiteTwoEndsScore family distance exponent chosenScale
              chosenCenter := by
  let candidates := scales ×ˢ centers
  let score : Real × alpha -> Real := fun pair =>
    finiteTwoEndsScore family distance exponent pair.1 pair.2
  have hcandidates : candidates.Nonempty := hscales.product hcenters
  obtain ⟨chosen, hchosen, hmax⟩ :=
    Finset.exists_mem_eq_sup' hcandidates score
  have hchosenMem := Finset.mem_product.mp hchosen
  refine ⟨chosen.1, hchosenMem.1, chosen.2, hchosenMem.2, ?_⟩
  intro radius hradius center hcenter
  have hcandidate : (radius, center) ∈ candidates :=
    Finset.mem_product.mpr ⟨hradius, hcenter⟩
  have hle : score (radius, center) <=
      candidates.sup' hcandidates score :=
    Finset.le_sup' score hcandidate
  rw [hmax] at hle
  exact hle

/-- Specialization where centers are the family itself, as in the actual
Lemma 5.7 application with fixed `g` in `G'(R)`. -/
theorem exists_familyCentered_finiteTwoEndsScore_maximizer
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real)
    (hscales : scales.Nonempty) (hfamily : family.Nonempty) :
    exists chosenScale, chosenScale ∈ scales ∧
      exists chosenCenter, chosenCenter ∈ family ∧
        forall radius, radius ∈ scales -> forall center, center ∈ family ->
          finiteTwoEndsScore family distance exponent radius center <=
            finiteTwoEndsScore family distance exponent chosenScale
              chosenCenter :=
  exists_finiteTwoEndsScore_maximizer family family scales distance exponent
    hscales hfamily

#print axioms finiteBallCount
#print axioms finiteTwoEndsScore
#print axioms exists_finiteTwoEndsScore_maximizer
#print axioms exists_familyCentered_finiteTwoEndsScore_maximizer

end


end FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
