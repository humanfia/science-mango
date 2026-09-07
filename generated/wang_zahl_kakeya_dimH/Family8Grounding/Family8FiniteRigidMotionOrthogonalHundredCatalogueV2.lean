import Family8Grounding.Family8FiniteRigidMotionOrthogonalNetCapCoverV3
import Family8Grounding.Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalHundredCatalogueV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteRigidMotionUnitSpherePackingV3
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalPatternCatalogueMembershipV2
open Family8FiniteRigidMotionOrthogonalNetCapCoverV3

noncomputable section

/-!
# A literal finite rotation catalogue for all hundred-tube tests

Use the sphere net at the natural 601-times-delta directional scale. Every
literal rotated containment event is first put in its two caps and then moved
to a net centre at the enlarged radius. The incidence-pattern catalogue
therefore gives a simultaneous quadratic count bound for every source tube,
every target tube, and every fixed translation.
-/

def hundredDirectionCap (delta : NNReal) : NNReal :=
  (601 : NNReal) * delta

theorem hundredDirectionCap_pos
    {delta : NNReal} (hdelta : 0 < delta) :
    0 < hundredDirectionCap delta :=
  mul_pos (by norm_num) hdelta

def enlargedHundredDirectionCap (delta : NNReal) : NNReal :=
  hundredDirectionCap delta + 2 * hundredDirectionCap delta

theorem enlargedHundredDirectionCap_pos
    {delta : NNReal} (hdelta : 0 < delta) :
    0 < enlargedHundredDirectionCap delta := by
  unfold enlargedHundredDirectionCap
  exact add_pos (hundredDirectionCap_pos hdelta)
    (mul_pos (by norm_num) (hundredDirectionCap_pos hdelta))

abbrev HundredDirectionChoice
    (delta : NNReal) (hdelta : 0 < delta) :=
  UnitDirectionChoice (hundredDirectionCap delta)
    (hundredDirectionCap_pos hdelta)

noncomputable instance hundredDirectionChoiceDecidableEq
    (delta : NNReal) (hdelta : 0 < delta) :
    DecidableEq (HundredDirectionChoice delta hdelta) :=
  Classical.decEq _

variable {source : Type*} [Fintype source] [DecidableEq source]
  {delta : NNReal}

def sourceTubeDirection
    (T : source -> Tube delta) (i : source) : Space :=
  (T i).axis.direction

def hundredNetDirection
    (delta : NNReal) (hdelta : 0 < delta)
    (k : HundredDirectionChoice delta hdelta) : Space :=
  k.1

abbrev HundredOrthogonalSample
    (T : source -> Tube delta) (hdelta : 0 < delta) (n : Nat) :=
  OrthogonalPatternSample
    (sourceTubeDirection T)
    (hundredNetDirection delta hdelta)
    (enlargedHundredDirectionCap delta) n

def sampledHundredOrthogonal
    (T : source -> Tube delta) (hdelta : 0 < delta) {n : Nat}
    (g : HundredOrthogonalSample T hdelta n) :
    OrthogonalThree :=
  sampledOrthogonal
    (sourceTubeDirection T)
    (hundredNetDirection delta hdelta)
    (enlargedHundredDirectionCap delta) g

def sampledHundredContainmentFinset
    (T : source -> Tube delta) (hdelta : 0 < delta) (n : Nat)
    (i : source) (W : Tube delta) (t : Space) :
    Finset (HundredOrthogonalSample T hdelta n) :=
  @Finset.filter (HundredOrthogonalSample T hdelta n)
    (fun g =>
      sampledHundredOrthogonal T hdelta g ∈
        orthogonalHundredContainmentEvent (T i) W t)
    (fun g => Classical.propDecidable
      (sampledHundredOrthogonal T hdelta g ∈
        orthogonalHundredContainmentEvent (T i) W t))
    Finset.univ

theorem card_sampledHundredContainmentFinset_le
    (T : source -> Tube delta) (hdelta : 0 < delta)
    (henlargedHalf : enlargedHundredDirectionCap delta ≤ 1 / 2)
    (n : Nat)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest source
              (HundredDirectionChoice delta hdelta))) : Real) ≤
        (n : Real) * (enlargedHundredDirectionCap delta : Real) ^ 2)
    (i : source) (W : Tube delta) (t : Space) :
    ((sampledHundredContainmentFinset
        T hdelta n i W t).card : Real) ≤
      (Fintype.card (HundredOrthogonalSample T hdelta n) : Real) *
        (11 * (enlargedHundredDirectionCap delta : Real) ^ 2) := by
  classical
  let base := hundredDirectionCap delta
  let enlarged := enlargedHundredDirectionCap delta
  have hbasePos : 0 < base := by
    simpa only [base] using hundredDirectionCap_pos hdelta
  obtain ⟨k, hnet⟩ :=
    exists_unitDirectionChoice_twoCap_cover
      (sourceTubeDirection T i) W.axis.direction
      W.axis.norm_direction base hbasePos base
  have hcontainBase :
      orthogonalHundredContainmentEvent (T i) W t ⊆
        orthogonalTwoCapEvent
          (sourceTubeDirection T i) W.axis.direction base := by
    simpa only [sourceTubeDirection, base, hundredDirectionCap] using
      orthogonalHundredContainmentEvent_subset_twoCapEvent
        (T i) W t hdelta
  have hcontainNet :
      orthogonalHundredContainmentEvent (T i) W t ⊆
        orthogonalTwoCapEvent
          (sourceTubeDirection T i) (k.1 : Space) enlarged := by
    have h := hcontainBase.trans hnet
    simpa only [enlarged, enlargedHundredDirectionCap, base] using h
  have hfinset :
      sampledHundredContainmentFinset T hdelta n i W t ⊆
        sampledTwoCapFinset
          (sourceTubeDirection T)
          (hundredNetDirection delta hdelta)
          (enlargedHundredDirectionCap delta) n (i, k) := by
    intro g hg
    have hgContain :
        sampledHundredOrthogonal T hdelta g ∈
          orthogonalHundredContainmentEvent (T i) W t := by
      unfold sampledHundredContainmentFinset at hg
      exact (Finset.mem_filter.mp hg).2
    apply (mem_sampledTwoCapFinset_iff
      (sourceTubeDirection T)
      (hundredNetDirection delta hdelta)
      (enlargedHundredDirectionCap delta) g (i, k)).2
    have hgNet := hcontainNet hgContain
    simpa only [sampledHundredOrthogonal, hundredNetDirection] using hgNet
  have hcard :
      ((sampledHundredContainmentFinset T hdelta n i W t).card : Real) ≤
        ((sampledTwoCapFinset
          (sourceTubeDirection T)
          (hundredNetDirection delta hdelta)
          (enlargedHundredDirectionCap delta) n (i, k)).card : Real) := by
    exact_mod_cast Finset.card_le_card hfinset
  have hcap :=
    card_sampledTwoCapFinset_le_card_mul_eleven_sq
      (sourceTubeDirection T)
      (hundredNetDirection delta hdelta)
      (fun q => unitDirectionChoice_norm
        (hundredDirectionCap delta)
        (hundredDirectionCap_pos hdelta) q)
      (enlargedHundredDirectionCap delta)
      (enlargedHundredDirectionCap_pos hdelta)
      henlargedHalf n hround (i, k)
  exact hcard.trans hcap

#print axioms hundredDirectionCap_pos
#print axioms enlargedHundredDirectionCap_pos
#print axioms card_sampledHundredContainmentFinset_le

end
end Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
