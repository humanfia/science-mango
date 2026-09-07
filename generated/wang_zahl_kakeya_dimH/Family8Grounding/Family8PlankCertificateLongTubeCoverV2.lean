import Family8Grounding.Family8PlankThickControlCanonicalSeedNormalizationV3
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankCertificateLongTubeCoverV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8CertifiedPlankPairOverlapV2
open Family8PlankThickControlCanonicalSeedNormalizationV3

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {C a b : NNReal} {K : ConvexBody Space}

/-- The unit long-axis segment through the center of an actual plank
certificate. -/
def plankCertificateLongAxis
    (cert : PlankDimensionsCertificate C a b K) : UnitSegment where
  base := cert.box.center - (2 : Real)⁻¹ • cert.box.frame 2
  direction := cert.box.frame 2
  norm_direction := cert.box.frame.norm_eq_one 2

/-- The genuine radius-`b` tube around the certified long axis. -/
def plankCertificateLongTube
    (cert : PlankDimensionsCertificate C a b K) : Tube b where
  axis := plankCertificateLongAxis cert

@[simp] theorem plankCertificateLongTube_axis
    (cert : PlankDimensionsCertificate C a b K) :
    (plankCertificateLongTube cert).axis = plankCertificateLongAxis cert :=
  rfl

/-- Every actual `a x b x 1` plank lies in the genuine radius-`b` tube
around the long axis of its selected box certificate. -/
theorem plankCertificate_body_subset_longTube
    (cert : PlankDimensionsCertificate C a b K) :
    (K : Set Space) ⊆ (plankCertificateLongTube cert).carrier := by
  intro x hx
  have hxbox : x ∈ cert.box.carrier := cert.outer_le hx
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff] at hxbox
  let c : Space := cert.box.center
  let d : Fin 3 → Real := fun k =>
    ⟪cert.box.frame k, x⟫_Real - ⟪cert.box.frame k, c⟫_Real
  have hd0 : |d 0| ≤ (a : Real) / 2 := by
    simpa [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      cert.side_eq, plankSides, NNReal.coe_div] using hxbox (0 : Fin 3)
  have hd1 : |d 1| ≤ (b : Real) / 2 := by
    simpa [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      cert.side_eq, plankSides, NNReal.coe_div] using hxbox (1 : Fin 3)
  have hd2 : |d 2| ≤ (2 : Real)⁻¹ := by
    simpa [d, c, FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      cert.side_eq, plankSides, NNReal.coe_div] using hxbox (2 : Fin 3)
  let t : Real := (2 : Real)⁻¹ + d 2
  have ht : t ∈ Set.Icc (0 : Real) 1 := by
    rw [abs_le] at hd2
    constructor <;> dsimp [t] <;> linarith [hd2.1, hd2.2]
  have hsum : ∑ k, d k • cert.box.frame k = x - c := by
    simpa [d, inner_sub_right] using cert.box.frame.sum_repr' (x - c)
  have hsum3 :
      d 0 • cert.box.frame 0 + d 1 • cert.box.frame 1 +
          d 2 • cert.box.frame 2 = x - c := by
    simpa [Fin.sum_univ_three] using hsum
  have hxyvec :
      x - ((plankCertificateLongTube cert).axis.base +
        t • (plankCertificateLongTube cert).axis.direction) =
          d 0 • cert.box.frame 0 + d 1 • cert.box.frame 1 := by
    calc
      x - ((plankCertificateLongTube cert).axis.base +
          t • (plankCertificateLongTube cert).axis.direction) =
          (x - c) +
            (c - ((plankCertificateLongTube cert).axis.base +
              t • (plankCertificateLongTube cert).axis.direction)) := by
        abel
      _ = (d 0 • cert.box.frame 0 + d 1 • cert.box.frame 1 +
            d 2 • cert.box.frame 2) +
            (c - ((plankCertificateLongTube cert).axis.base +
              t • (plankCertificateLongTube cert).axis.direction)) := by
        rw [hsum3]
      _ = d 0 • cert.box.frame 0 + d 1 • cert.box.frame 1 := by
        simp only [plankCertificateLongTube, plankCertificateLongAxis, c, t]
        module
  have hdist :
      dist x ((plankCertificateLongTube cert).axis.base +
          t • (plankCertificateLongTube cert).axis.direction) ≤ (b : Real) := by
    rw [dist_eq_norm, hxyvec]
    calc
      ‖d 0 • cert.box.frame 0 + d 1 • cert.box.frame 1‖ ≤
          ‖d 0 • cert.box.frame 0‖ + ‖d 1 • cert.box.frame 1‖ :=
        norm_add_le _ _
      _ = |d 0| + |d 1| := by
        simp [norm_smul, cert.box.frame.norm_eq_one]
      _ ≤ (a : Real) / 2 + (b : Real) / 2 := add_le_add hd0 hd1
      _ ≤ (b : Real) := by
        have hab : (a : Real) ≤ (b : Real) := by exact_mod_cast cert.a_le_b
        linarith
  exact Metric.mem_cthickening_of_dist_le x
    ((plankCertificateLongTube cert).axis.base +
      t • (plankCertificateLongTube cert).axis.direction)
    (b : Real) (plankCertificateLongTube cert).axis.carrier
    ((plankCertificateLongTube cert).axis.mem_carrier_of_mem_Icc ht) hdist

variable {a b : NNReal}

/-- The same-index genuine `b`-tube cover of an arbitrary actual shaded
plank family. The refinement is the literal full finite index set. -/
def plankLongTubeCoverFamily
    (D : ShadedConvexPlankFamily iota a b) : UniformTubeFamily b iota where
  tubes i := plankCertificateLongTube (plankSeedCertificate D i)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem plankLongTubeCoverFamily_tubes
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    (plankLongTubeCoverFamily D).tubes i =
      plankCertificateLongTube (plankSeedCertificate D i) := rfl

theorem sourcePlank_subset_longTubeCover
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    (D.family i : Set Space) ⊆
      ((plankLongTubeCoverFamily D).tubes i).carrier :=
  plankCertificate_body_subset_longTube (plankSeedCertificate D i)

/-- The source shaded sets, now typed against the genuine tube cover. -/
def plankLongTubeCoverShading
    (D : ShadedConvexPlankFamily iota a b) :
    Shading (plankLongTubeCoverFamily D).bodyFamily where
  carrier := D.shading.carrier
  measurable_carrier := D.shading.measurable_carrier
  carrier_subset i :=
    (D.shading.carrier_subset i).trans (sourcePlank_subset_longTubeCover D i)

@[simp] theorem plankLongTubeCoverShading_carrier
    (D : ShadedConvexPlankFamily iota a b) (i : iota) :
    (plankLongTubeCoverShading D).carrier i = D.shading.carrier i := rfl

theorem plankLongTubeCoverShading_shadingMass
    (D : ShadedConvexPlankFamily iota a b) :
    (plankLongTubeCoverShading D).shadingMass = D.shading.shadingMass := rfl

theorem plankLongTubeCoverShading_shadedUnion
    (D : ShadedConvexPlankFamily iota a b) :
    (plankLongTubeCoverShading D).shadedUnion = D.shading.shadedUnion := rfl

theorem plankLongTubeCoverShading_averageMultiplicity
    (D : ShadedConvexPlankFamily iota a b) :
    (plankLongTubeCoverShading D).averageMultiplicity =
      D.shading.averageMultiplicity := rfl

theorem source_familyVolume_le_longTubeCover
    (D : ShadedConvexPlankFamily iota a b) :
    familyVolume D.family ≤ familyVolume (plankLongTubeCoverFamily D).bodyFamily := by
  unfold familyVolume
  apply Finset.sum_le_sum
  intro i _hi
  exact measure_mono (sourcePlank_subset_longTubeCover D i)

theorem longTubeCover_familyVolume_le_card_mul_eight_sq
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) :
    familyVolume (plankLongTubeCoverFamily D).bodyFamily ≤
      (Fintype.card iota : ENNReal) * (8 * (b : ENNReal) ^ 2) := by
  unfold familyVolume
  calc
    (∑ i : iota,
        volume ((plankLongTubeCoverFamily D).bodyFamily i : Set Space)) ≤
        ∑ _i : iota, 8 * (b : ENNReal) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact ((plankLongTubeCoverFamily D).tubes i).volume_le_eight_mul_sq_of_le_half hb
    _ = (Fintype.card iota : ENNReal) * (8 * (b : ENNReal) ^ 2) := by
      simp

#print axioms plankCertificateLongTube_axis
#print axioms plankCertificate_body_subset_longTube
#print axioms plankLongTubeCoverFamily_tubes
#print axioms sourcePlank_subset_longTubeCover
#print axioms plankLongTubeCoverShading_carrier
#print axioms plankLongTubeCoverShading_shadingMass
#print axioms plankLongTubeCoverShading_shadedUnion
#print axioms plankLongTubeCoverShading_averageMultiplicity
#print axioms source_familyVolume_le_longTubeCover
#print axioms longTubeCover_familyVolume_le_card_mul_eight_sq

end
end Family8PlankCertificateLongTubeCoverV2
