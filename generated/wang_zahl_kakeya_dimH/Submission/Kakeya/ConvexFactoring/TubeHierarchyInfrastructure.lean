import Submission.Kakeya.Uniformity.TubeFamily

open Set
open scoped NNReal

/-!
# Tube-hierarchy infrastructure

This module supplies the radius-changing, buffering, restriction, and reindexing
operations needed to construct tube hierarchies with exact Lean types.

Buffered families are indexed by their effective radii: buffering a `δ`-tube
by `ε` produces a genuine `(δ + ε)`-tube.  Similarly, an arbitrary restriction
does not silently inherit a quantitative refinement loss.  The loss-preserving
operation therefore requires its new cardinality estimate explicitly, while
the unrestricted subtype operation installs a fresh scale-empty refinement.

This is infrastructure only.  In particular, this module does not assert the
existence of a `CoarseTubePartition`, a `TubeHierarchy`, or a compatible
multiscale hierarchy from an arbitrary family of tubes.
-/

namespace Submission.Kakeya.ConvexGeometry

namespace Tube

/-- Change only the certified radius of a tube, retaining its unit axis. -/
def changeRadius {δ : NNReal} (T : Tube δ) (ρ : NNReal) : Tube ρ where
  axis := T.axis

@[simp]
theorem changeRadius_axis {δ : NNReal} (T : Tube δ) (ρ : NNReal) :
    (T.changeRadius ρ).axis = T.axis :=
  rfl

@[simp]
theorem changeRadius_carrier {δ : NNReal} (T : Tube δ) (ρ : NNReal) :
    (T.changeRadius ρ).carrier = Metric.cthickening (ρ : ℝ) T.axis.carrier :=
  rfl

/-- Increasing the certified radius only enlarges the carrier. -/
theorem carrier_subset_changeRadius {δ ρ : NNReal} (T : Tube δ) (hδρ : δ ≤ ρ) :
    T.carrier ⊆ (T.changeRadius ρ).carrier := by
  exact Metric.cthickening_mono (by exact_mod_cast hδρ) T.axis.carrier

/-- Add a nonnegative buffer to a tube while retaining its unit axis. -/
def buffer {δ : NNReal} (T : Tube δ) (ε : NNReal) : Tube (δ + ε) :=
  T.changeRadius (δ + ε)

@[simp]
theorem buffer_axis {δ : NNReal} (T : Tube δ) (ε : NNReal) :
    (T.buffer ε).axis = T.axis :=
  rfl

/-- Buffering a tube is exactly closed metric thickening of its carrier. -/
theorem buffer_carrier {δ : NNReal} (T : Tube δ) (ε : NNReal) :
    (T.buffer ε).carrier = Metric.cthickening (ε : ℝ) T.carrier := by
  rw [Tube.carrier, Tube.carrier, cthickening_cthickening]
  · congr 1
    exact_mod_cast add_comm δ ε
  · positivity
  · positivity

/-- A tube is contained in each of its nonnegative buffers. -/
theorem carrier_subset_buffer {δ : NNReal} (T : Tube δ) (ε : NNReal) :
    T.carrier ⊆ (T.buffer ε).carrier := by
  rw [buffer_carrier]
  exact Metric.self_subset_cthickening _

/-- Thickening respects both carrier containment and buffer monotonicity. -/
theorem buffer_subset_buffer_of_subset_of_le
    {δ ρ ε η : NNReal} {T : Tube δ} {U : Tube ρ}
    (hTU : T.carrier ⊆ U.carrier) (hεη : ε ≤ η) :
    (T.buffer ε).carrier ⊆ (U.buffer η).carrier := by
  rw [buffer_carrier, buffer_carrier]
  exact (Metric.cthickening_subset_of_subset (ε : ℝ) hTU).trans
    (Metric.cthickening_mono (by exact_mod_cast hεη) U.carrier)

/-- The recursive-buffer step: a raw `c`-neighborhood containment remains an
exact containment after buffering the child by `q` and the parent by `c + q`. -/
theorem buffer_subset_buffer_add_of_subset_cthickening
    {δ ρ c q : NNReal} {T : Tube δ} {U : Tube ρ}
    (hTU : T.carrier ⊆ Metric.cthickening (c : ℝ) U.carrier) :
    (T.buffer q).carrier ⊆ (U.buffer (c + q)).carrier := by
  rw [buffer_carrier, buffer_carrier]
  have h := Metric.cthickening_subset_of_subset (q : ℝ) hTU
  rw [cthickening_cthickening (by positivity) (by positivity)] at h
  simpa [NNReal.coe_add, add_comm, add_left_comm, add_assoc] using h

/-- Equal child and parent buffers preserve an existing carrier containment. -/
theorem buffer_subset_buffer_of_subset
    {δ ρ ε : NNReal} {T : Tube δ} {U : Tube ρ}
    (hTU : T.carrier ⊆ U.carrier) :
    (T.buffer ε).carrier ⊆ (U.buffer ε).carrier :=
  buffer_subset_buffer_of_subset_of_le hTU le_rfl

end Tube

end Submission.Kakeya.ConvexGeometry

namespace Submission.Kakeya.Uniformity

/-- A loss-one refinement supported on an arbitrary finite active set.  It has
no prescribed scales, so its uniformity obligation is vacuous. -/
def UniformRefinement.ofFinset {α : Type*} [DecidableEq α]
    (active : Finset α) : UniformRefinement α where
  profile :=
    { family := active
      scales := ∅
      label := fun _ _ => ⟨0⟩ }
  refined := active
  refined_subset := Finset.Subset.rfl
  uniform := by simp [MultiscaleProfile.UniformOn]
  loss := 1
  card_le_loss_mul := by simp

@[simp]
theorem UniformRefinement.ofFinset_refined {α : Type*} [DecidableEq α]
    (active : Finset α) :
    (UniformRefinement.ofFinset active).refined = active :=
  rfl

/-- Restrict a refinement while preserving its profile and its scale labels.
The new quantitative loss is explicit input, since an arbitrary restriction
need not retain any fixed fraction of the old family. -/
def UniformRefinement.restrictWithLoss
    {α : Type*} [DecidableEq α] (R : UniformRefinement α)
    (selected : Finset α) (hselected : selected ⊆ R.refined)
    (newLoss : Nat)
    (hcard : R.profile.family.card ≤ newLoss * selected.card) :
    UniformRefinement α where
  profile := R.profile
  refined := selected
  refined_subset := hselected.trans R.refined_subset
  uniform := by
    intro r hr
    obtain ⟨level, hlevel⟩ := R.uniform r hr
    exact ⟨level, fun x hx => hlevel x (hselected hx)⟩
  loss := newLoss
  card_le_loss_mul := hcard

@[simp]
theorem UniformRefinement.restrictWithLoss_refined
    {α : Type*} [DecidableEq α] (R : UniformRefinement α)
    (selected : Finset α) (hselected : selected ⊆ R.refined)
    (newLoss : Nat)
    (hcard : R.profile.family.card ≤ newLoss * selected.card) :
    (R.restrictWithLoss selected hselected newLoss hcard).refined = selected :=
  rfl

/-- Transport a certified refinement across an index equivalence. -/
def UniformRefinement.reindex
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : UniformRefinement α) (e : α ≃ β) : UniformRefinement β where
  profile :=
    { family := R.profile.family.map e.toEmbedding
      scales := R.profile.scales
      label := fun r y => R.profile.label r (e.symm y) }
  refined := R.refined.map e.toEmbedding
  refined_subset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨x, R.refined_subset hx, rfl⟩
  uniform := by
    intro r hr
    obtain ⟨level, hlevel⟩ := R.uniform r hr
    refine ⟨level, ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    subst y
    simpa using hlevel x hx
  loss := R.loss
  card_le_loss_mul := by
    simpa using R.card_le_loss_mul

@[simp]
theorem UniformRefinement.reindex_refined
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : UniformRefinement α) (e : α ≃ β) :
    (R.reindex e).refined = R.refined.map e.toEmbedding :=
  rfl

namespace UniformTubeFamily

open Submission.Kakeya.ConvexGeometry

/-- Change every tube radius, preserving axes and the certified refinement. -/
def changeRadius {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (ρ : NNReal) : UniformTubeFamily ρ ι where
  tubes := fun i => (family.tubes i).changeRadius ρ
  refinement := family.refinement

@[simp]
theorem changeRadius_tubes {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (ρ : NNReal) (i : ι) :
    (family.changeRadius ρ).tubes i = (family.tubes i).changeRadius ρ :=
  rfl

/-- Buffer every tube in a uniform family by the same radius. -/
def buffer {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (ε : NNReal) :
    UniformTubeFamily (δ + ε) ι where
  tubes := fun i => (family.tubes i).buffer ε
  refinement := family.refinement

@[simp]
theorem buffer_tubes {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (ε : NNReal) (i : ι) :
    (family.buffer ε).tubes i = (family.tubes i).buffer ε :=
  rfl

theorem tube_carrier_subset_changeRadius
    {δ ρ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (hδρ : δ ≤ ρ) (i : ι) :
    (family.tubes i).carrier ⊆ ((family.changeRadius ρ).tubes i).carrier :=
  (family.tubes i).carrier_subset_changeRadius hδρ

/-- Reindex a uniform tube family along an equivalence. -/
def reindex {δ : NNReal} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (family : UniformTubeFamily δ ι) (e : ι ≃ κ) : UniformTubeFamily δ κ where
  tubes := fun k => family.tubes (e.symm k)
  refinement := family.refinement.reindex e

@[simp]
theorem reindex_tubes {δ : NNReal} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (family : UniformTubeFamily δ ι) (e : ι ≃ κ) (k : κ) :
    (family.reindex e).tubes k = family.tubes (e.symm k) :=
  rfl

/-- Restrict a tube family to a finite active subtype.  The new family uses a
fresh loss-one, scale-empty refinement on the subtype; quantitative retention
must be supplied separately when needed. -/
def restrictTo {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (active : Finset ι) :
    UniformTubeFamily δ {i // i ∈ active} where
  tubes := fun i => family.tubes i.1
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem restrictTo_tubes {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (active : Finset ι)
    (i : {i // i ∈ active}) :
    (family.restrictTo active).tubes i = family.tubes i.1 :=
  rfl

@[simp]
theorem restrictTo_refined {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (active : Finset ι) :
    (family.restrictTo active).refinement.refined = Finset.univ :=
  rfl

/-- Keep the original index type and tube map, but replace the certified
refinement by an explicitly quantified sub-refinement. -/
def restrictRefinementWithLoss
    {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι)
    (selected : Finset ι) (hselected : selected ⊆ family.refinement.refined)
    (newLoss : Nat)
    (hcard : family.refinement.profile.family.card ≤ newLoss * selected.card) :
    UniformTubeFamily δ ι where
  tubes := family.tubes
  refinement := family.refinement.restrictWithLoss selected hselected newLoss hcard

@[simp]
theorem restrictRefinementWithLoss_refined
    {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι)
    (selected : Finset ι) (hselected : selected ⊆ family.refinement.refined)
    (newLoss : Nat)
    (hcard : family.refinement.profile.family.card ≤ newLoss * selected.card) :
    (family.restrictRefinementWithLoss selected hselected newLoss hcard).refinement.refined =
      selected :=
  rfl

end UniformTubeFamily

end Submission.Kakeya.Uniformity
