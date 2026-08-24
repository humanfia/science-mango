import FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1

open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1

noncomputable section

/-!
# Canonical finite two-ends maximizers

The exact maximizer theorem already proves existence on finite nonempty
scale and center carriers.  This module makes one such maximizer into a
canonical function of the input data.  The selected scale can therefore be
bucketed simultaneously across a finite collection of points or
rectangles, as required by the dyadic pigeonholing preceding PYZ Lemma 5.7.
-/

variable {alpha : Type*}

/-- Data of one exact family-centered weighted-score maximizer. -/
structure CanonicalMaximizerData
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real) where
  scale : Real
  scale_mem : scale ∈ scales
  center : alpha
  center_mem : center ∈ family
  dominates : forall radius, radius ∈ scales ->
    forall testCenter, testCenter ∈ family ->
      finiteTwoEndsScore family distance exponent radius testCenter <=
        finiteTwoEndsScore family distance exponent scale center

/-- Select one exact maximizer from the proved finite existence theorem. -/
noncomputable def canonicalMaximizerData
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real)
    (hscales : scales.Nonempty) (hfamily : family.Nonempty) :
    CanonicalMaximizerData family scales distance exponent := by
  classical
  let hexists := exists_familyCentered_finiteTwoEndsScore_maximizer
    family scales distance exponent hscales hfamily
  let scale := Classical.choose hexists
  let hscaleExists := Classical.choose_spec hexists
  let hscaleMem := hscaleExists.1
  let hcenterExists := hscaleExists.2
  let center := Classical.choose hcenterExists
  have hcenterSpec := Classical.choose_spec hcenterExists
  exact
    { scale := scale
      scale_mem := hscaleMem
      center := center
      center_mem := hcenterSpec.1
      dominates := hcenterSpec.2 }

/-- The canonical selected scale belongs to the carrier. -/
theorem canonicalMaximizerData_scale_mem
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real)
    (hscales : scales.Nonempty) (hfamily : family.Nonempty) :
    (canonicalMaximizerData family scales distance exponent
      hscales hfamily).scale ∈ scales :=
  (canonicalMaximizerData family scales distance exponent
    hscales hfamily).scale_mem

/-- Universal exact score domination carried by the canonical choice. -/
theorem canonicalMaximizerData_dominates
    (family : Finset alpha) (scales : Finset Real)
    (distance : alpha -> alpha -> Real) (exponent : Real)
    (hscales : scales.Nonempty) (hfamily : family.Nonempty)
    (radius : Real) (hradius : radius ∈ scales)
    (center : alpha) (hcenter : center ∈ family) :
    finiteTwoEndsScore family distance exponent radius center <=
      finiteTwoEndsScore family distance exponent
        (canonicalMaximizerData family scales distance exponent
          hscales hfamily).scale
        (canonicalMaximizerData family scales distance exponent
          hscales hfamily).center :=
  (canonicalMaximizerData family scales distance exponent
    hscales hfamily).dominates radius hradius center hcenter

#print axioms CanonicalMaximizerData
#print axioms canonicalMaximizerData
#print axioms canonicalMaximizerData_scale_mem
#print axioms canonicalMaximizerData_dominates

end

end FamilyStickyCinematicL32Lemma57CanonicalMaximizerV1
