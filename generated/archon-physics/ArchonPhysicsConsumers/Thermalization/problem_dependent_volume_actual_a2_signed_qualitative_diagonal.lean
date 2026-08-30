import ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
open Filter MeasureTheory
open scoped Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
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
  exact
    exists_positive_diagonal_of_actualSignedA2_of_mismatchLaw
      ensemble datum hN R hR hradiusMeasurable hradiusBound hmismatchLaw

#print axioms exists_positive_diagonal_of_actualSignedA2_pointwiseL1
#print axioms exists_positive_diagonal_of_actualSignedA2_of_mismatchLaw

example {Omega : Type*} [MeasurableSpace Omega]
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
  exact
    exists_positive_thermodynamic_diagonal_of_actualSignedA2_of_mismatchLaw
      ensemble datum hvolume hN R hR hradiusMeasurable hradiusBound
        hmismatchLaw

#print axioms
  exists_positive_thermodynamic_diagonal_of_actualSignedA2_of_mismatchLaw

end

end ArchonPhysicsConsumers.Thermalization
