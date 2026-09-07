import Family8Grounding.Family8StickyScaleCoverAutomaticDef212FieldsV1
import Family8Grounding.Family8NormalizedLongIntervalRelevantDef212InputsV5
import Mathlib.Tactic

/-!
# Relevant finite Definition 2.12 inputs from upper partitioning alone

At finitely many sequence endpoints, the automatic John/CWA constants can be
combined into one natural constant.  C-uniformity is automatic with the fine
index cardinality constant.  Consequently the only structural input still
needed to construct `RelevantFiniteSequenceDef212Inputs` is doubled-parent
partitioning of the upper cover at each relevant long interval.

The resulting constant is data-dependent.  This theorem deliberately does
not claim a small-delta-uniform bound for it.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8RelevantDef212AutomaticNonpartitionProducerV1

open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FiniteFibreAutomaticCWAV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalRelevantDef212InputsV5
open Family8StickyScaleCoverAutomaticDef212FieldsV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- Literal lower endpoint cover used by the relevant finite package. -/
def automaticTauCover
    {fine : UniformTubeFamily delta iota}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    StickyScaleCover fine (S.tau m) :=
  C.base.cover (S.tau m) (S.delta_le_tau m)
    ((S.tau_le_theta m).trans (S.theta_le_one m))

/-- Literal upper endpoint cover used by the relevant finite package. -/
def automaticThetaCover
    {fine : UniformTubeFamily delta iota}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    StickyScaleCover fine (S.theta m) :=
  C.base.cover (S.theta m)
    ((S.delta_le_tau m).trans (S.tau_le_theta m))
    (S.theta_le_one m)

/-- Canonical John geometry at the lower endpoint. -/
noncomputable def automaticTauJohnGeometry
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    UnitRescalingGeometry (automaticTauCover C S m) :=
  Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
    (automaticTauCover C S m)
    (hD.delta_pos.trans_le (S.delta_le_tau m))
    ((S.tau_le_theta m).trans (S.theta_le_one m))

/-- Canonical John geometry at the upper endpoint. -/
noncomputable def automaticThetaJohnGeometry
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    UnitRescalingGeometry (automaticThetaCover C S m) :=
  Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
    (automaticThetaCover C S m)
    (hD.delta_pos.trans_le
      ((S.delta_le_tau m).trans (S.tau_le_theta m)))
    (S.theta_le_one m)

/-- All five non-partition fields of the relevant finite package are
automatic with one finite data-dependent constant. -/
theorem exists_relevantFiniteSequenceDef212Inputs_of_theta_partition
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (epsilon : Real)
    (hpartition : forall m : Fin depth, S.IsLong epsilon m ->
      IsDoubledParentPartitioning (automaticThetaCover C S m)) :
    exists K : NNReal,
      Nonempty (RelevantFiniteSequenceDef212Inputs C S epsilon K) := by
  have htauExists : forall m : Fin depth,
      exists Cnn : Nat, 1 <= Cnn ∧
        (automaticTauJohnGeometry D hD C S m).FibresSatisfyCWA
          (Cnn : ENNReal) := by
    intro m
    exact exists_nat_fibresSatisfyCWA_of_volume_pos
      (automaticTauJohnGeometry D hD C S m)
      (Family8StickyScaleCoverAutomaticDef212FieldsV1.StickyScaleCover.rescaledFiberFamily_volume_pos
        (automaticTauCover C S m) hD.delta_pos
        (automaticTauJohnGeometry D hD C S m))
  have hthetaExists : forall m : Fin depth,
      exists Cnn : Nat, 1 <= Cnn ∧
        (automaticThetaJohnGeometry D hD C S m).FibresSatisfyCWA
          (Cnn : ENNReal) := by
    intro m
    exact exists_nat_fibresSatisfyCWA_of_volume_pos
      (automaticThetaJohnGeometry D hD C S m)
      (Family8StickyScaleCoverAutomaticDef212FieldsV1.StickyScaleCover.rescaledFiberFamily_volume_pos
        (automaticThetaCover C S m) hD.delta_pos
        (automaticThetaJohnGeometry D hD C S m))
  choose Ktau hKtauOne hKtauCWA using htauExists
  choose Ktheta hKthetaOne hKthetaCWA using hthetaExists
  let cwaSum : Nat :=
    ∑ m : Fin depth, (Ktau m + Ktheta m)
  let Knn : Nat := automaticCUniformNat iota + cwaSum
  have hpair_le_sum (m : Fin depth) :
      Ktau m + Ktheta m <= cwaSum := by
    dsimp only [cwaSum]
    exact Finset.single_le_sum
      (fun j _hj => Nat.zero_le (Ktau j + Ktheta j))
      (Finset.mem_univ m)
  have hKtau_le (m : Fin depth) : Ktau m <= Knn := by
    have hp := hpair_le_sum m
    dsimp only [Knn]
    omega
  have hKtheta_le (m : Fin depth) : Ktheta m <= Knn := by
    have hp := hpair_le_sum m
    dsimp only [Knn]
    omega
  have hautomatic_le : automaticCUniformNat iota <= Knn := by
    dsimp only [Knn]
    omega
  refine ⟨(Knn : NNReal), ?_⟩
  refine ⟨
    { tau_c_uniform := ?_
      theta_doubled_parent_partitioning := ?_
      tau_unitRescalingGeometry := ?_
      tau_rescaled_fibres_cwa := ?_
      theta_unitRescalingGeometry := ?_
      theta_rescaled_fibres_cwa := ?_ }⟩
  · intro m _hlong
    exact isCUniform_mono
      (Family8StickyScaleCoverAutomaticDef212FieldsV1.StickyScaleCover.isCUniform_automatic
        (automaticTauCover C S m)) (by
          exact_mod_cast hautomatic_le)
  · intro m hlong
    simpa only [automaticThetaCover] using hpartition m hlong
  · intro m _hlong
    exact automaticTauJohnGeometry D hD C S m
  · intro m _hlong
    change (automaticTauJohnGeometry D hD C S m).FibresSatisfyCWA
      (((Knn : NNReal) : ENNReal))
    exact fibresSatisfyCWA_mono (hKtauCWA m) (by
      exact_mod_cast hKtau_le m)
  · intro m _hlong
    exact automaticThetaJohnGeometry D hD C S m
  · intro m _hlong
    change (automaticThetaJohnGeometry D hD C S m).FibresSatisfyCWA
      (((Knn : NNReal) : ENNReal))
    exact fibresSatisfyCWA_mono (hKthetaCWA m) (by
      exact_mod_cast hKtheta_le m)

#print axioms automaticTauJohnGeometry
#print axioms automaticThetaJohnGeometry
#print axioms
  exists_relevantFiniteSequenceDef212Inputs_of_theta_partition

end
end Family8RelevantDef212AutomaticNonpartitionProducerV1
