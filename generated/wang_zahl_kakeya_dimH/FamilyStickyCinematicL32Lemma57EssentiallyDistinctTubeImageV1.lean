import Family4GlobalExtremalUpstream

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream

noncomputable section

/-!
# Actual Tube image of an essentially-distinct indexed family

For positive radius, volume-overlap essential distinctness rules out two
different active indices carrying the same actual tube.  Consequently the
finite image in the concrete `Tube` type retains the active cardinality.
This is the lossless index-to-carrier bridge needed before coefficient-space
deduplication; it does not claim a quantitative near-coefficient cap.
-/

/-- Positive-radius essential distinctness makes the actual tube map
injective on the active indices. -/
theorem tubes_injectiveOn_active_of_essentiallyDistinct
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.InjOn fine.tubes (active : Set iota) := by
  intro i hi j hj htube
  by_contra hij
  have hdistinct := hpair hi hj hij
  change EssentiallyDistinct (fine.tubes i) (fine.tubes j) at hdistinct
  rw [htube, EssentiallyDistinct, Set.inter_self, max_self] at hdistinct
  let v : ENNReal := volume (fine.tubes j).carrier
  have hvPos : 0 < v := by
    exact (fine.tubes j).volume_pos hdelta
  have hvTop : v ≠ ∞ := ne_of_lt (fine.tubes j).volume_lt_top
  have hhalfTop : (2 : ENNReal)⁻¹ * v ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hvTop
  have hreal := ENNReal.toReal_mono hhalfTop hdistinct
  have hvRealPos : 0 < v.toReal := ENNReal.toReal_pos hvPos.ne' hvTop
  change v.toReal <= (((2 : ENNReal)⁻¹ * v).toReal) at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal
  norm_num at hreal
  linarith

/-- The concrete finite family obtained by imaging active indices. -/
noncomputable def activeTubeImage
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota) :
    Finset (Tube delta) := by
  classical
  exact active.image fine.tubes

/-- Every tube in the concrete image comes from an active index. -/
theorem mem_activeTubeImage_iff
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (T : Tube delta) :
    T ∈ activeTubeImage fine active ↔
      exists i, i ∈ active ∧ fine.tubes i = T := by
  classical
  simp [activeTubeImage]

/-- The concrete image has exactly the active cardinality. -/
theorem activeTubeImage_card
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    (activeTubeImage fine active).card = active.card := by
  classical
  rw [activeTubeImage]
  exact Finset.card_image_iff.mpr fun i hi j hj htube =>
    tubes_injectiveOn_active_of_essentiallyDistinct fine active hdelta hpair
      hi hj htube

#print axioms tubes_injectiveOn_active_of_essentiallyDistinct
#print axioms mem_activeTubeImage_iff
#print axioms activeTubeImage_card

end


end FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
