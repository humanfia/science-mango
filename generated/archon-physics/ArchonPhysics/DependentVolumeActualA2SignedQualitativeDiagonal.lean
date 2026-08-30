import ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
import ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
import ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal

/-!
# Signed-frame dependent-volume actual A2 diagonal

This module packages the measurable signed-frame actual `A2` observable for
channel data whose finite volume varies with the index.  A qualitative `L1`
certificate at every fixed volume yields a positive weak-coupling diagonal
along which the signed physical `g^2` accumulation on the `g^-2` window tends
to zero.

The certificates can in turn be constructed from absolute continuity of the
unweighted actual mismatch law, measurable radius coordinates, and a finite
radius bound.  No legacy eigenvector-sign measurability premise appears.
As with every pointwise diagonal, no uniform-in-volume rate or prescribed
power law between volume and coupling is asserted.
-/

namespace ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The signed-frame external weak-coupling accumulation for a datum with a
dependently stored finite volume. -/
def signedExternalWeakCouplingAccumulation
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) (g : Real) : Real :=
  letI : NeZero datum.N := datum.neZero
  actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
    datum.channel datum.kappa datum.radius datum.observed datum.term g

/-- Signed-frame qualitative `L1` certificate with the datum's positive
volume instance restored locally. -/
abbrev SignedStaticL1Certificate
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) : Type :=
  letI : NeZero datum.N := datum.neZero
  ActualSignedIteratedA2StaticL1FourierCertificate ensemble datum.channel
    datum.kappa datum.radius datum.observed datum.term

/-- Absolute continuity of the datum's unweighted actual mismatch law. -/
abbrev MismatchLawAbsolutelyContinuous
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) : Prop :=
  letI : NeZero datum.N := datum.neZero
  physlibIteratedA2MismatchLaw ensemble datum.channel datum.observed datum.term ≪
    (volume : Measure Real)

/-- Restore the local volume and apply the signed fixed-volume qualitative
kinetic closure. -/
theorem tendsto_signedExternalWeakCouplingAccumulation_of_certificate
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (certificate : SignedStaticL1Certificate datum ensemble) :
    Tendsto (signedExternalWeakCouplingAccumulation datum ensemble)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let _ : NeZero datum.N := datum.neZero
  exact
    tendsto_actualSignedIteratedA2StaticExternalWeakCoupling_of_certificate
      ensemble datum.channel datum.kappa datum.radius datum.observed datum.term
        certificate

/-- Construct the signed `L1` certificate for one dependent-volume datum
directly from mismatch-law absolute continuity and measurable bounded radii. -/
def signedStaticL1Certificate_of_mismatchLaw_absolutelyContinuous
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (hN : 2 <= datum.N) (R : Real) (hR : 0 <= R)
    (hradiusMeasurable : forall mode,
      Measurable fun sample => datum.radius sample mode)
    (hradiusBound : forall sample mode, |datum.radius sample mode| <= R)
    (hmismatchLaw : MismatchLawAbsolutelyContinuous datum ensemble) :
    SignedStaticL1Certificate datum ensemble := by
  let _ : NeZero datum.N := datum.neZero
  exact
    actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      ensemble hN datum.channel datum.kappa R hR datum.radius
        hradiusMeasurable hradiusBound datum.observed datum.term hmismatchLaw

/-- Every fixed-volume signed certificate gives an honest simultaneous
large-index/weak-coupling diagonal for the actual physical accumulations. -/
theorem exists_positive_diagonal_of_actualSignedA2_pointwiseL1
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat -> DependentActualA2ChannelDatum Omega)
    (certificate : forall n,
      SignedStaticL1Certificate (datum n) ensemble) :
    exists coupling : Nat -> Real,
      (forall n, 0 < coupling n) ∧
      (forall n, coupling n < 1 / ((n : Real) + 1)) ∧
      (forall n,
        signedExternalWeakCouplingAccumulation
            (datum n) ensemble (coupling n) <
          1 / ((n : Real) + 1)) ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n => signedExternalWeakCouplingAccumulation
          (datum n) ensemble (coupling n))
        atTop (nhds 0) := by
  obtain ⟨coupling, hpositive, hupper, habs, hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_pointwise_nhdsGT_zero
      (fun n g => signedExternalWeakCouplingAccumulation (datum n) ensemble g)
      (fun n =>
        tendsto_signedExternalWeakCouplingAccumulation_of_certificate
          (datum n) ensemble (certificate n))
  refine ⟨coupling, hpositive, hupper, ?_, hcoupling, haccumulation⟩
  intro n
  exact lt_of_le_of_lt (le_abs_self _) (habs n)

/-- Concrete diagonal constructor using only unweighted mismatch-law absolute
continuity and measurable bounded signed-frame data at each finite volume. -/
theorem exists_positive_diagonal_of_actualSignedA2_of_mismatchLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat -> DependentActualA2ChannelDatum Omega)
    (hN : forall n, 2 <= (datum n).N)
    (R : Nat -> Real) (hR : forall n, 0 <= R n)
    (hradiusMeasurable : forall n mode,
      Measurable fun sample => (datum n).radius sample mode)
    (hradiusBound : forall n sample mode,
      |(datum n).radius sample mode| <= R n)
    (hmismatchLaw : forall n,
      MismatchLawAbsolutelyContinuous (datum n) ensemble) :
    exists coupling : Nat -> Real,
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n => signedExternalWeakCouplingAccumulation
          (datum n) ensemble (coupling n))
        atTop (nhds 0) := by
  let certificate : forall n,
      SignedStaticL1Certificate (datum n) ensemble := fun n =>
    signedStaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      (datum n) ensemble (hN n) (R n) (hR n)
        (hradiusMeasurable n) (hradiusBound n) (hmismatchLaw n)
  obtain ⟨coupling, _hpositive, _hupper, _hbound,
      hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_actualSignedA2_pointwiseL1
      ensemble datum certificate
  exact ⟨coupling, hcoupling, haccumulation⟩

/-- Thermodynamic formulation of the same diagonal.  The additional premise
states explicitly that the finite volumes stored in the data tend to
infinity; it is preserved in the conclusion rather than being conflated with
the weak-coupling choice. -/
theorem exists_positive_thermodynamic_diagonal_of_actualSignedA2_of_mismatchLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat -> DependentActualA2ChannelDatum Omega)
    (hvolume : Tendsto (fun n => (datum n).N) atTop atTop)
    (hN : forall n, 2 <= (datum n).N)
    (R : Nat -> Real) (hR : forall n, 0 <= R n)
    (hradiusMeasurable : forall n mode,
      Measurable fun sample => (datum n).radius sample mode)
    (hradiusBound : forall n sample mode,
      |(datum n).radius sample mode| <= R n)
    (hmismatchLaw : forall n,
      MismatchLawAbsolutelyContinuous (datum n) ensemble) :
    exists coupling : Nat -> Real,
      (forall n, 0 < coupling n) ∧
      Tendsto (fun n => (datum n).N) atTop atTop ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n => signedExternalWeakCouplingAccumulation
          (datum n) ensemble (coupling n))
        atTop (nhds 0) := by
  let certificate : forall n,
      SignedStaticL1Certificate (datum n) ensemble := fun n =>
    signedStaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      (datum n) ensemble (hN n) (R n) (hR n)
        (hradiusMeasurable n) (hradiusBound n) (hmismatchLaw n)
  obtain ⟨coupling, hpositive, _hupper, _hbound,
      hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_actualSignedA2_pointwiseL1
      ensemble datum certificate
  exact ⟨coupling, hpositive, hvolume, hcoupling, haccumulation⟩

end

end ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
