import Family8Grounding.Family8SelectedParentPlankFineAxisCoordinateV2
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8SelectedParentPlankFineProxyDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AffineImageAxisPlankCoordinateBridgeV4
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterFrameBoxPackingV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Literal fine-axis proxy datum for one actual selected parent plank

The proxy axis is the unit extension of the real fine axis after the same
bucket affine map used to define the selected parent plank.  Its shading is
empty because this module is purely geometric; later fresh selection uses
its cardinality and conflict graph, not a false mass statement.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A scale-`s` project tube on the unit extension of one real affine image
axis. -/
def affineAxisProxyTube (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (T : Tube delta) : Tube s where
  axis := affineImageUnitExtensionAxis e T

@[simp] theorem affineAxisProxyTube_axis
    (s : NNReal) (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    (affineAxisProxyTube s e T).axis = affineImageUnitExtensionAxis e T :=
  rfl

/-- The actual fine fibre of `W`, with every axis transformed by the one
common bucket map. -/
def selectedPlankFineProxyFamily
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    UniformTubeFamily s (SelectedPlankFineIndex S W) where
  tubes i := affineAxisProxyTube s (bucketNormalizedAffineEquiv e label)
    (fine.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem selectedPlankFineProxyFamily_tubes
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    (selectedPlankFineProxyFamily s e S B hrho label W).tubes i =
      affineAxisProxyTube s (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1) :=
  rfl

/-- Canonical empty shading for a purely geometric indexed family. -/
def emptyShading {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : NNReal} (F : UniformTubeFamily s ι) : Shading F.bodyFamily where
  carrier _ := ∅
  measurable_carrier _ := MeasurableSet.empty
  carrier_subset _ := Set.empty_subset _

/-- The actual proxy datum used by normalized fresh selection on one `W`.
No analytic mass is asserted by this datum. -/
def selectedPlankFineProxyDatum
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    ActualTubeDatum s (SelectedPlankFineIndex S W) where
  family := selectedPlankFineProxyFamily s e S B hrho label W
  shading := emptyShading _

@[simp] theorem selectedPlankFineProxyDatum_family_tubes
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    (selectedPlankFineProxyDatum s e S B hrho label W).family.tubes i =
      affineAxisProxyTube s (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1) :=
  rfl

/-- The canonical certificate box of `W` contains every real affine-axis
midpoint from its literal fine fibre. -/
theorem selectedPlankFine_affineCenter_mem_chosenBox
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1) ∈ (chosenPlankCertificate hplank W).box.carrier := by
  let cert := chosenPlankCertificate hplank W
  have haxis := selectedPlankFine_axis_image_subset_parent
    e S B hrho label W i
  have hbaseK : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.base ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨(fine.tubes i.1).axis.base,
      (fine.tubes i.1).axis.base_mem_carrier, rfl⟩
  have hendK : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.endpoint ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨(fine.tubes i.1).axis.endpoint,
      (fine.tubes i.1).axis.endpoint_mem_carrier, rfl⟩
  have hbase : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hend : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  exact affineImageAxisCenter_mem_frameBox
    (bucketNormalizedAffineEquiv e label) (fine.tubes i.1)
      cert.box hbase hend

/-- The same canonical box gives a uniform distance-two center bound on the
whole actual fine fibre. -/
theorem selectedPlankFine_affineCenter_dist_chosenBoxCenter_le_two
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ‖affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1) - (chosenPlankCertificate hplank W).box.center‖ ≤ 2 := by
  let cert := chosenPlankCertificate hplank W
  have hcenter : affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
      (fine.tubes i.1) ∈ cert.box.carrier := by
    exact selectedPlankFine_affineCenter_mem_chosenBox
      e S B hrho label hplank W i
  have haOne : bucketShortA label ≤ 1 := cert.a_le_b.trans cert.b_le_one
  have haReal : (bucketShortA label : Real) ≤ 1 := by exact_mod_cast haOne
  have hbReal : (bucketShortB label : Real) ≤ 1 := by
    exact_mod_cast cert.b_le_one
  have hsum : ((∑ j, cert.box.side j : NNReal) : Real) ≤ 4 := by
    rw [cert.side_eq, Fin.sum_univ_three]
    simp only [plankSides, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    norm_num only [NNReal.coe_add, NNReal.coe_one]
    linarith
  have hdist := frameBox_dist_center_le_half_sum_side cert.box hcenter
  rw [dist_eq_norm] at hdist
  exact hdist.trans (by nlinarith)

/-- Canonical raw-vector bounds in the fixed chosen frame of `W`. -/
theorem selectedPlankFine_rawVector_chosenFrame_bounds
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    |⟪(chosenPlankCertificate hplank W).box.frame 0,
      affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)⟫_Real| ≤ (bucketShortA label : Real) ∧
    |⟪(chosenPlankCertificate hplank W).box.frame 1,
      affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)⟫_Real| ≤ (bucketShortB label : Real) := by
  let cert := chosenPlankCertificate hplank W
  have haxis := selectedPlankFine_axis_image_subset_parent
    e S B hrho label W i
  have hbaseK : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.base ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨(fine.tubes i.1).axis.base,
      (fine.tubes i.1).axis.base_mem_carrier, rfl⟩
  have hendK : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.endpoint ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨(fine.tubes i.1).axis.endpoint,
      (fine.tubes i.1).axis.endpoint_mem_carrier, rfl⟩
  have hbase : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hend : bucketNormalizedAffineEquiv e label
      (fine.tubes i.1).axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  have h0 := abs_inner_affineImageAxisVector_le_frameBox_side
    (bucketNormalizedAffineEquiv e label) (fine.tubes i.1)
      cert.box hbase hend 0
  have h1 := abs_inner_affineImageAxisVector_le_frameBox_side
    (bucketNormalizedAffineEquiv e label) (fine.tubes i.1)
      cert.box hbase hend 1
  rw [cert.side_eq] at h0 h1
  constructor
  · simpa [plankSides] using h0
  · simpa [plankSides] using h1

#print axioms affineAxisProxyTube
#print axioms selectedPlankFineProxyDatum
#print axioms selectedPlankFine_affineCenter_mem_chosenBox
#print axioms selectedPlankFine_affineCenter_dist_chosenBoxCenter_le_two
#print axioms selectedPlankFine_rawVector_chosenFrame_bounds

end
end Family8SelectedParentPlankFineProxyDatumV1
