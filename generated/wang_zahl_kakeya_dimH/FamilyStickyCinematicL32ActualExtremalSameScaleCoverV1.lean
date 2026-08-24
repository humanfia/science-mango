import FamilyStickyCinematicL32ActualSameScaleCoverParallelLossCapV1
import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

universe u v

/-!
# Actual same-scale covers from the primitive extremal-family field

The extremal-family record already supplies a literal scale cover and a
parallel-cluster bound at every scale between delta and one.  We choose its
delta-scale member once and restrict only its active domain to each projected
incidence fibre.  Parent tubes and cluster cardinalities remain unchanged.
-/

/-- Restriction of only the active fine domain of a literal scale cover. -/
def restrictActualTubeScaleCover
    {delta tau : NNReal} {iota : Type u} [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {ambient active : Finset iota}
    (C : @TubeScaleCover delta tau iota _ fine ambient)
    (hsubset : active ⊆ ambient) :
    @TubeScaleCover delta tau iota _ fine active where
  count := C.count
  tubes := C.tubes
  parent := C.parent
  carrier_subset := by
    intro i hi
    exact C.carrier_subset i (hsubset hi)

@[simp]
theorem restrictActualTubeScaleCover_parallelCluster
    {delta tau : NNReal} {iota : Type u} [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {ambient active : Finset iota}
    (C : @TubeScaleCover delta tau iota _ fine ambient)
    (hsubset : active ⊆ ambient) (U : Tube tau) :
    (restrictActualTubeScaleCover C hsubset).parallelCluster U =
      C.parallelCluster U := rfl

/-- Canonical choice of the primitive extremal cover at the original tube
scale. -/
noncomputable def actualExtremalSameScaleCover
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y ambient parallelLoss
      epsilon sigma) :
    @TubeScaleCover delta delta iota _ fine ambient :=
  Classical.choose <| G.scale_covers delta le_rfl <|
    G.delta_le_half.trans (by norm_num)

theorem actualExtremalSameScaleCover_cluster_bound
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y ambient parallelLoss
      epsilon sigma) (U : Tube delta) :
    ((actualExtremalSameScaleCover G).parallelCluster U).card ≤
      parallelLoss := by
  exact Classical.choose_spec
    (G.scale_covers delta le_rfl
      (G.delta_le_half.trans (by norm_num))) U

/-- The actual extremal cover restricted to one literal projected active
fibre. -/
noncomputable def actualExtremalProjectedActiveCover
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y ambient parallelLoss
      epsilon sigma)
    (Z : FiniteProjectedShading point iota)
    (hambient : Z.ambient ⊆ ambient) (x : point) :
    @TubeScaleCover delta delta iota _ fine (Z.activeAtPoint x) :=
  restrictActualTubeScaleCover (actualExtremalSameScaleCover G) <| by
    intro i hi
    exact hambient ((Z.mem_activeAtPoint x i).mp hi).1

theorem actualExtremalProjectedActiveCover_cluster_bound
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {ambient : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y ambient parallelLoss
      epsilon sigma)
    (Z : FiniteProjectedShading point iota)
    (hambient : Z.ambient ⊆ ambient) (x : point) (U : Tube delta) :
    ((actualExtremalProjectedActiveCover G Z hambient x).parallelCluster U).card ≤
      parallelLoss := by
  change ((actualExtremalSameScaleCover G).parallelCluster U).card ≤ parallelLoss
  exact actualExtremalSameScaleCover_cluster_bound G U

#print axioms restrictActualTubeScaleCover
#print axioms actualExtremalSameScaleCover
#print axioms actualExtremalSameScaleCover_cluster_bound
#print axioms actualExtremalProjectedActiveCover
#print axioms actualExtremalProjectedActiveCover_cluster_bound

end

end FamilyStickyCinematicL32ActualExtremalSameScaleCoverV1
