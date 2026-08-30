import ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
import ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
import ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal

/-!
# A pointwise-volume diagonal for actual A2 channels

The actual `A2` qualitative closure is a theorem at each fixed finite
volume.  This file records the strongest thermodynamic statement that follows
from those pointwise limits alone: for any sequence of finite-volume channel
data carrying `L1` mismatch certificates, one can choose a positive coupling
`g n -> 0` along which the corresponding physical external-`g`
accumulations tend to zero.

The choice of `g n` may depend on the entire volume sequence.  Consequently
this is an existence diagonal, not a uniform-in-volume estimate and not a
power-law relation between volume and coupling.
-/

namespace ArchonPhysics.DependentVolumeActualA2QualitativeL1Diagonal

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal
open Filter Set
open scoped Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An `L1` mismatch-density certificate for a datum whose finite volume is
stored dependently inside the datum. -/
abbrev StaticL1Certificate
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) : Type :=
  letI : NeZero datum.N := datum.neZero
  ActualIteratedA2StaticL1FourierCertificate ensemble datum.channel
    datum.kappa datum.radius datum.observed datum.term

/-- Restore the datum's local positive-volume instance and apply the actual
fixed-volume qualitative `L1` closure. -/
theorem tendsto_externalWeakCouplingAccumulation_qualitativeL1
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (certificate : StaticL1Certificate datum ensemble) :
    Tendsto (datum.externalWeakCouplingAccumulation ensemble)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let _ : NeZero datum.N := datum.neZero
  exact
    tendsto_actualIteratedA2StaticExternalWeakCoupling_qualitativeL1
      ensemble datum.channel datum.kappa datum.radius datum.observed datum.term
        certificate

/-- Pointwise fixed-volume `L1` certificates give an honest simultaneous
large-index/weak-coupling diagonal.  The selected physical accumulation is
smaller than `1 / (n + 1)` and hence tends to zero, but no quantitative rule
for selecting `coupling n` is claimed. -/
theorem exists_positive_diagonal_of_actualA2_pointwiseL1
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat -> DependentActualA2ChannelDatum Omega)
    (certificate : forall n, StaticL1Certificate (datum n) ensemble) :
    exists coupling : Nat -> Real,
      (forall n, 0 < coupling n) ∧
      (forall n, coupling n < 1 / ((n : Real) + 1)) ∧
      (forall n,
        (datum n).externalWeakCouplingAccumulation ensemble (coupling n) <
          1 / ((n : Real) + 1)) ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (datum n).externalWeakCouplingAccumulation ensemble (coupling n))
        atTop (nhds 0) := by
  obtain ⟨coupling, hpositive, hupper, habs, hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_pointwise_nhdsGT_zero
      (fun n g => (datum n).externalWeakCouplingAccumulation ensemble g)
      (fun n =>
        tendsto_externalWeakCouplingAccumulation_qualitativeL1
          (datum n) ensemble (certificate n))
  refine ⟨coupling, hpositive, hupper, ?_, hcoupling, haccumulation⟩
  intro n
  exact lt_of_le_of_lt (le_abs_self _) (habs n)

end

end ArchonPhysics.DependentVolumeActualA2QualitativeL1Diagonal
