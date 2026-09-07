import Family8Grounding.Family8StickySelectedFineSubtypeScaleCoverV1
import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineDenseFiberV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Density-good fibre of a literal selected-fine Sticky cover

The literal selected fine family is partitioned by its occupied parent image.
Exact body-mass and shaded-mass decompositions therefore select one actual
parent fibre whose density is at least the global selected-family density.
No factor two is needed.  Nonzero selected mass also makes this same fibre's
actual shaded union positive.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Fibre body mass of the selected-fine factorization is exactly the family
volume of the literal fibre subtype. -/
theorem selectedFine_fiberBodyMass_eq_familyVolume
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (k : Fin (selectedFineParentValues S selected).card) :
    fiberBodyMass
        (toConvexFactorization
          (selectedFineScaleCover S selected hselected)) k =
      familyVolume
        ((selectedFineScaleCover S selected hselected).fiberFamily k) := by
  classical
  let T := selectedFineScaleCover S selected hselected
  change (∑ i ∈ T.fiber k,
      volume ((selectedFineFamily S selected).bodyFamily i : Set Space)) =
    ∑ i : {i // i ∈ T.fiber k},
      volume (T.fiberFamily k i : Set Space)
  simp only [StickyScaleCover.fiberFamily]
  exact Finset.sum_subtype (M := ℝ≥0∞) (T.fiber k) (fun _i => Iff.rfl) _

/-- Fibre shading mass is exactly the mass of the literal source-fibre
shading consumed by the contracted-John endpoint. -/
theorem selectedFine_fiberShadingMass_eq_sourceShadingMass
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (Y : Shading fine.bodyFamily)
    (k : Fin (selectedFineParentValues S selected).card) :
    fiberShadingMass
        (toConvexFactorization
          (selectedFineScaleCover S selected hselected))
        (selectedFineShading S selected Y) k =
      (stickyFiberSourceShading
        (selectedFineScaleCover S selected hselected)
        (selectedFineShading S selected Y) k).shadingMass := by
  classical
  let T := selectedFineScaleCover S selected hselected
  let Z := selectedFineShading S selected Y
  change (∑ i ∈ T.fiber k, volume (Z.carrier i)) =
    ∑ i : {i // i ∈ T.fiber k},
      volume ((stickyFiberSourceShading T Z k).carrier i)
  simp only [stickyFiberSourceShading_carrier]
  exact Finset.sum_subtype (M := ℝ≥0∞) (T.fiber k) (fun _i => Iff.rfl) _

/-- A nonzero selected shading has one occupied parent fibre whose literal
subtype density is at least the selected global density; the same fibre has
positive actual shaded-union volume. -/
theorem exists_selectedFine_denseFiber
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (Y : Shading fine.bodyFamily) (hdelta : 0 < delta)
    (hmass : (selectedFineShading S selected Y).shadingMass ≠ 0) :
    ∃ k : {k // k ∈
        (selectedFineScaleCover S selected hselected).activeCoarse},
      (selectedFineShading S selected Y).shadingDensity <=
        (stickyFiberSourceShading
          (selectedFineScaleCover S selected hselected)
          (selectedFineShading S selected Y) k.1).shadingDensity ∧
      0 < volume
        (stickyFiberSourceShading
          (selectedFineScaleCover S selected hselected)
          (selectedFineShading S selected Y) k.1).shadedUnion := by
  classical
  let T := selectedFineScaleCover S selected hselected
  let Z := selectedFineShading S selected Y
  let P := toConvexFactorization T
  let lambda := Z.shadingDensity
  have hselectedNonempty : selected.Nonempty := by
    by_contra hnot
    have hempty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    subst selected
    apply hmass
    unfold Shading.shadingMass
    simp
  have hcoarse : P.index.coarse.Nonempty := by
    obtain ⟨i, hi⟩ := hselectedNonempty
    let p : SelectedFineParentIndex S selected :=
      ⟨S.parent i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let q : Fin (selectedFineParentValues S selected).card :=
      (selectedFineParentValues S selected).equivFin p
    refine ⟨q, ?_⟩
    simp [P, T]
  have hbody : activeBodyMass P =
      familyVolume (selectedFineFamily S selected).bodyFamily := by
    unfold activeBodyMass familyVolume P T
    simp
  have hshading : activeShadingMass P Z = Z.shadingMass := by
    unfold activeShadingMass Shading.shadingMass P T
    simp
  have hglobal : lambda * activeBodyMass P = activeShadingMass P Z := by
    rw [hbody, hshading]
    exact
      InducedShadingDensityAlgebra.shadingDensity_mul_familyVolume Z
  have hsum :
      (∑ k ∈ P.index.coarse,
          lambda * fiberBodyMass P k) <=
        ∑ k ∈ P.index.coarse, fiberShadingMass P Z k := by
    calc
      (∑ k ∈ P.index.coarse,
          lambda * fiberBodyMass P k) =
          lambda * ∑ k ∈ P.index.coarse, fiberBodyMass P k := by
        rw [Finset.mul_sum]
      _ = lambda * activeBodyMass P := by
        rw [activeBodyMass_eq_sum_fiberBodyMass]
      _ = activeShadingMass P Z := hglobal
      _ <= ∑ k ∈ P.index.coarse, fiberShadingMass P Z k := by
        rw [activeShadingMass_eq_sum_fiberShadingMass]
  obtain ⟨k, hk, hkDensity⟩ :=
    ENNReal.exists_le_of_sum_le hcoarse hsum
  have hkT : k ∈ T.activeCoarse := by
    exact hk
  let kk : {k // k ∈ T.activeCoarse} := ⟨k, hkT⟩
  let fiberZ := stickyFiberSourceShading T Z k
  have hfiberBody : fiberBodyMass P k =
      familyVolume (T.fiberFamily k) := by
    simpa only [P, T] using
      selectedFine_fiberBodyMass_eq_familyVolume S selected hselected k
  have hfiberMass : fiberShadingMass P Z k = fiberZ.shadingMass := by
    simpa only [P, T, Z, fiberZ] using
      selectedFine_fiberShadingMass_eq_sourceShadingMass
        S selected hselected Y k
  have hfiberVolumePos : 0 < familyVolume (T.fiberFamily k) := by
    obtain ⟨i, hiActive, hiParent⟩ := T.parent_surjective k hkT
    have hiFiber : i ∈ T.fiber k :=
      (T.mem_fiber i k).2 ⟨hiActive, hiParent⟩
    have hsingle := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : {j // j ∈ T.fiber k} =>
        volume (T.fiberFamily k j : Set Space))
      (fun _ _ => bot_le)
      (Finset.mem_univ (⟨i, hiFiber⟩ : {j // j ∈ T.fiber k}))
    have htubePos : 0 <
        volume ((selectedFineFamily S selected).tubes i).carrier :=
      (selectedFineFamily S selected).tubes i |>.volume_pos hdelta
    apply htubePos.trans_le
    simpa [familyVolume, StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body] using hsingle
  have hdense : lambda <= fiberZ.shadingDensity := by
    unfold Shading.shadingDensity
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfiberVolumePos.ne')
      (Or.inl (familyVolume_ne_top (T.fiberFamily k)))).2
    rw [← hfiberBody, ← hfiberMass]
    exact hkDensity
  have hlambdaPos : 0 < lambda := by
    unfold lambda Z Shading.shadingDensity
    exact ENNReal.div_pos hmass
      (familyVolume_ne_top (selectedFineFamily S selected).bodyFamily)
  have hfiberDensityPos : 0 < fiberZ.shadingDensity :=
    hlambdaPos.trans_le hdense
  have hfiberMass0 : fiberZ.shadingMass ≠ 0 := by
    unfold Shading.shadingDensity at hfiberDensityPos
    exact (ENNReal.div_pos_iff.mp hfiberDensityPos).1
  have hfiberUnion0 : volume fiberZ.shadedUnion ≠ 0 :=
    volume_shadedUnion_ne_zero_of_shadingMass_ne_zero fiberZ hfiberMass0
  refine ⟨kk, ?_, bot_lt_iff_ne_bot.mpr hfiberUnion0⟩
  simpa only [kk, T, Z, lambda, fiberZ] using hdense

#print axioms selectedFine_fiberBodyMass_eq_familyVolume
#print axioms selectedFine_fiberShadingMass_eq_sourceShadingMass
#print axioms exists_selectedFine_denseFiber

end
end Family8StickySelectedFineDenseFiberV1
