import ArchonPhysics.ThermalizationTransfer

/-!
# An explicit supervolume joint limit for R32

This module shows that the quantification over admissible weak-coupling,
large-volume paths is non-vacuous for every prescribed size cutoff.  We use
the positive inverse-linear coupling

`g j = 1 / (j + 1)`

and choose the volume pointwise above both the supplied cutoff and the
integer ceiling of `g ^ (-12)`.  A further lower bound by `j` makes divergence
of the volume independent of any regularity of the supplied cutoff.
-/

namespace ArchonPhysics.R32SupervolumeJointLimit

open ArchonPhysics.ThermalizationTransfer
open Filter Set Topology

noncomputable section

/-- A concrete positive coupling sequence tending to zero. -/
def inverseLinearCoupling (j : Nat) : Real :=
  1 / ((j : Real) + 1)

/-- The requested integer volume floor `ceil (g ^ (-12))`. -/
def inverseTwelfthPowerCeiling (g : Real) : Nat :=
  Nat.ceil (g ^ (-12 : Int))

/-- A volume schedule above the arbitrary cutoff, the inverse-twelfth-power
floor, and the index itself. -/
def supervolumeSystemSize (sizeCutoff : Real → Nat) (j : Nat) : Nat :=
  max
    (max
      (sizeCutoff (inverseLinearCoupling j))
      (inverseTwelfthPowerCeiling (inverseLinearCoupling j)))
    j

theorem inverseLinearCoupling_pos (j : Nat) :
    0 < inverseLinearCoupling j := by
  unfold inverseLinearCoupling
  positivity

theorem inverseLinearCoupling_tendsto_zero :
    Tendsto inverseLinearCoupling atTop (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall inverseLinearCoupling_pos

theorem supervolumeSystemSize_ge_requestedFloor
    (sizeCutoff : Real → Nat) (j : Nat) :
    max
        (sizeCutoff (inverseLinearCoupling j))
        (inverseTwelfthPowerCeiling (inverseLinearCoupling j)) ≤
      supervolumeSystemSize sizeCutoff j := by
  exact Nat.le_max_left _ _

theorem supervolumeSystemSize_ge_index
    (sizeCutoff : Real → Nat) (j : Nat) :
    j ≤ supervolumeSystemSize sizeCutoff j := by
  exact Nat.le_max_right _ _

theorem supervolumeSystemSize_tendsto_atTop
    (sizeCutoff : Real → Nat) :
    Tendsto (supervolumeSystemSize sizeCutoff) atTop atTop := by
  refine tendsto_atTop.2 fun lowerBound => ?_
  filter_upwards [eventually_ge_atTop lowerBound] with j hj
  exact hj.trans (supervolumeSystemSize_ge_index sizeCutoff j)

/-- For every cutoff, an explicit admissible path whose volume dominates the
cutoff and `ceil (g ^ (-12))` at every index, not merely eventually. -/
def supervolumeJointLimit
    (sizeCutoff : Real → Nat) : AdmissibleJointLimit sizeCutoff where
  systemSize := supervolumeSystemSize sizeCutoff
  coupling := inverseLinearCoupling
  coupling_pos := inverseLinearCoupling_pos
  coupling_tendsto_zero := inverseLinearCoupling_tendsto_zero
  systemSize_tendsto_atTop := supervolumeSystemSize_tendsto_atTop sizeCutoff
  eventually_sizeCutoff := by
    exact Filter.Eventually.of_forall fun j =>
      (Nat.le_max_left
        (sizeCutoff (inverseLinearCoupling j))
        (inverseTwelfthPowerCeiling (inverseLinearCoupling j))).trans
      (supervolumeSystemSize_ge_requestedFloor sizeCutoff j)

theorem supervolumeJointLimit_dominates_requestedFloor
    (sizeCutoff : Real → Nat) (j : Nat) :
    max
        (sizeCutoff ((supervolumeJointLimit sizeCutoff).coupling j))
        (inverseTwelfthPowerCeiling
          ((supervolumeJointLimit sizeCutoff).coupling j)) ≤
      (supervolumeJointLimit sizeCutoff).systemSize j := by
  exact supervolumeSystemSize_ge_requestedFloor sizeCutoff j

/-- Explicit non-vacuity, retaining the full pointwise lower-bound witness. -/
theorem exists_admissibleJointLimit_dominating_inverseTwelfthPower
    (sizeCutoff : Real → Nat) :
    ∃ s : AdmissibleJointLimit sizeCutoff,
      ∀ j,
        max
            (sizeCutoff (s.coupling j))
            (Nat.ceil (s.coupling j ^ (-12 : Int))) ≤
          s.systemSize j := by
  refine ⟨supervolumeJointLimit sizeCutoff, ?_⟩
  intro j
  exact supervolumeJointLimit_dominates_requestedFloor sizeCutoff j

/-- In particular, `AdmissibleJointLimit sizeCutoff` is inhabited for every
function `sizeCutoff : Real → Nat`, with no monotonicity assumption. -/
theorem admissibleJointLimit_nonempty (sizeCutoff : Real → Nat) :
    Nonempty (AdmissibleJointLimit sizeCutoff) :=
  ⟨supervolumeJointLimit sizeCutoff⟩

end

end ArchonPhysics.R32SupervolumeJointLimit
