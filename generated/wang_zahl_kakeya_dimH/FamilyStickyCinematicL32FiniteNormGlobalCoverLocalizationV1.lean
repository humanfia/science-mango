import FamilyStickyCinematicL32FiniteNormCriticalBallV1
import FamilyStickyCinematicL32FiniteMetricMaximalCoverV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1

open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1

noncomputable section

/-!
# Local norm balls inside one global fixed-scale cover cell

The global centre is the actual code supplied by the maximal fixed-scale
cover of a finite ambient family.  The selected local centre itself witnesses
intersection of `B_x` with that global ball.  The metric three-ball lemma then
gives the paper containment `B_x ⊆ 3B`, and hence pointwise cardinal
retention after restricting the source family to `F ∩ 3B`.
-/

variable {alpha : Type*} [DecidableEq alpha]

/-- The paper's global localized family `F_B = F ∩ 3B`. -/
def finiteGlobalNormLocalizedFamily
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha) : Finset alpha :=
  finiteFamilyMetricBall family distance (3 * globalScale) globalCenter

set_option linter.unusedSectionVars false in
/-- The local critical centre lies in the fixed ambient family. -/
theorem finiteCriticalMaximizerCenter_mem_ambient
    (family ambient : Finset alpha) (distance : alpha → alpha → Real)
    (delta ceiling exponent : Real) (hfamily : family.Nonempty)
    (hsubset : family ⊆ ambient) :
    finiteCriticalMaximizerCenter family distance delta ceiling exponent
        hfamily ∈ ambient :=
  hsubset (finiteCriticalMaximizerCenter_mem family distance delta ceiling
    exponent hfamily)

/-- The local critical centre is an actual intersection witness between
`B_x` and the global cover ball assigned to it. -/
theorem finiteNormCriticalBall_intersects_global_code_ball
    (family ambient : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent globalScale : Real}
    (hfamily : family.Nonempty) (hsubset : family ⊆ ambient)
    (hsymm : ∀ f g, distance f g = distance g f)
    (hself : ∀ f, f ∈ ambient → distance f f = 0)
    (hdelta : 0 ≤ delta) (hdeltaCeiling : delta ≤ ceiling)
    (hglobalScale : 0 < globalScale) :
    let localCenter := finiteCriticalMaximizerCenter family distance delta
      ceiling exponent hfamily
    let centerMember : FiniteMetricMember ambient :=
      ⟨localCenter, finiteCriticalMaximizerCenter_mem_ambient family ambient
        distance delta ceiling exponent hfamily hsubset⟩
    let globalCenter := finiteMetricCoverCode ambient distance globalScale
      hsymm centerMember
    ∃ witness,
      witness ∈ finiteNormCriticalBall family distance delta ceiling
        exponent hfamily ∧
      witness ∈ finiteFamilyMetricBall ambient distance globalScale
        globalCenter := by
  dsimp only
  let localCenter := finiteCriticalMaximizerCenter family distance delta
    ceiling exponent hfamily
  have hlocalFamily : localCenter ∈ family :=
    finiteCriticalMaximizerCenter_mem family distance delta ceiling exponent
      hfamily
  have hlocalAmbient : localCenter ∈ ambient := hsubset hlocalFamily
  let centerMember : FiniteMetricMember ambient := ⟨localCenter, hlocalAmbient⟩
  let globalCenter := finiteMetricCoverCode ambient distance globalScale
    hsymm centerMember
  refine ⟨localCenter, ?_, ?_⟩
  · exact finiteCriticalMaximizerCenter_mem_finiteNormCriticalBall
      family distance hfamily
      (fun center hcenter => by
        rw [hself center (hsubset hcenter)]
        exact hdelta)
      hdeltaCeiling
  · rw [finiteFamilyMetricBall, Finset.mem_filter]
    refine ⟨hlocalAmbient, ?_⟩
    exact (distance_finiteMetricCoverCode_lt ambient distance hsymm
      (fun f hf => by rw [hself f hf]; exact hglobalScale) centerMember).le

/-- The actual cover code and the local scale-bin upper bound imply the
faithful containment `B_x ⊆ F ∩ 3B`. -/
theorem finiteNormCriticalBall_subset_global_code_localizedFamily
    (family ambient : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent globalScale : Real}
    (hfamily : family.Nonempty) (hsubset : family ⊆ ambient)
    (hsymm : ∀ f g, distance f g = distance g f)
    (htriangle : ∀ f center g,
      distance f g ≤ distance f center + distance center g)
    (hself : ∀ f, f ∈ ambient → distance f f = 0)
    (hdelta : 0 ≤ delta) (hdeltaCeiling : delta ≤ ceiling)
    (hglobalScale : 0 < globalScale)
    (hscaleUpper :
      finiteCriticalMaximizerScale family distance delta ceiling exponent
        hfamily ≤ globalScale) :
    let localCenter := finiteCriticalMaximizerCenter family distance delta
      ceiling exponent hfamily
    let centerMember : FiniteMetricMember ambient :=
      ⟨localCenter, finiteCriticalMaximizerCenter_mem_ambient family ambient
        distance delta ceiling exponent hfamily hsubset⟩
    let globalCenter := finiteMetricCoverCode ambient distance globalScale
      hsymm centerMember
    finiteNormCriticalBall family distance delta ceiling exponent hfamily ⊆
      finiteGlobalNormLocalizedFamily family distance globalScale
        globalCenter := by
  dsimp only
  let localCenter := finiteCriticalMaximizerCenter family distance delta
    ceiling exponent hfamily
  have hlocalFamily : localCenter ∈ family :=
    finiteCriticalMaximizerCenter_mem family distance delta ceiling exponent
      hfamily
  have hlocalAmbient : localCenter ∈ ambient := hsubset hlocalFamily
  let centerMember : FiniteMetricMember ambient := ⟨localCenter, hlocalAmbient⟩
  let globalCenter := finiteMetricCoverCode ambient distance globalScale
    hsymm centerMember
  have hcode : distance localCenter globalCenter ≤ globalScale :=
    (distance_finiteMetricCoverCode_lt ambient distance hsymm
      (fun f hf => by rw [hself f hf]; exact hglobalScale)
      centerMember).le
  have hlocalSelf : distance localCenter localCenter ≤
      finiteCriticalMaximizerScale family distance delta ceiling exponent
        hfamily := by
    rw [hself localCenter hlocalAmbient]
    exact hdelta.trans
      (finiteCriticalMaximizerScale_bounds family distance hfamily
        hdeltaCeiling).1
  have hmetricSubset := finiteFamilyMetricBall_subset_three_of_intersects
    family distance localCenter globalCenter localCenter hsymm htriangle
    hscaleUpper hlocalSelf hcode
  intro f hf
  apply hmetricSubset
  simpa only [finiteFamilyMetricBall, finiteNormCriticalBall] using hf

/-- Pointwise restriction to the global `3B` cell retains at least the
literal norm critical-ball cardinality. -/
theorem finiteNormCriticalBall_card_le_global_code_localizedFamily_card
    (family ambient : Finset alpha) (distance : alpha → alpha → Real)
    {delta ceiling exponent globalScale : Real}
    (hfamily : family.Nonempty) (hsubset : family ⊆ ambient)
    (hsymm : ∀ f g, distance f g = distance g f)
    (htriangle : ∀ f center g,
      distance f g ≤ distance f center + distance center g)
    (hself : ∀ f, f ∈ ambient → distance f f = 0)
    (hdelta : 0 ≤ delta) (hdeltaCeiling : delta ≤ ceiling)
    (hglobalScale : 0 < globalScale)
    (hscaleUpper :
      finiteCriticalMaximizerScale family distance delta ceiling exponent
        hfamily ≤ globalScale) :
    let localCenter := finiteCriticalMaximizerCenter family distance delta
      ceiling exponent hfamily
    let centerMember : FiniteMetricMember ambient :=
      ⟨localCenter, finiteCriticalMaximizerCenter_mem_ambient family ambient
        distance delta ceiling exponent hfamily hsubset⟩
    let globalCenter := finiteMetricCoverCode ambient distance globalScale
      hsymm centerMember
    (finiteNormCriticalBall family distance delta ceiling exponent
      hfamily).card ≤
      (finiteGlobalNormLocalizedFamily family distance globalScale
        globalCenter).card := by
  dsimp only
  exact Finset.card_le_card
    (finiteNormCriticalBall_subset_global_code_localizedFamily
      family ambient distance hfamily hsubset hsymm htriangle hself hdelta
      hdeltaCeiling hglobalScale hscaleUpper)

#print axioms finiteGlobalNormLocalizedFamily
#print axioms finiteCriticalMaximizerCenter_mem_ambient
#print axioms finiteNormCriticalBall_intersects_global_code_ball
#print axioms finiteNormCriticalBall_subset_global_code_localizedFamily
#print axioms finiteNormCriticalBall_card_le_global_code_localizedFamily_card

end

end FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
