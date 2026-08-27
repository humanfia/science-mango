import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds
import ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay

/-!
# On-shell recombination of the canonical decay sectors

Broadening by the normalized squared-sinc kernel is additive in the source
finite measure.  Combining this exact identity with the parent--child
`O(T^{-1/2})` cluster theorem shows that the complete four-sector on-shell
coefficient is determined by only the all-distinct and child-repeated
clusters.

The final theorem accepts separate Lebesgue densities for those two main
sectors.  Thus no artificial global-density premise is imposed on the full
collision law: the two parent--child sectors may remain singular, because
their broadened contributions have already been proved to vanish.
-/

open scoped Topology

namespace ArchonPhysics.DecayChannelSectorClusterOnShellRecombination

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds
open ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open Filter MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Fixed-time broadening is exactly additive in its source finite measure. -/
theorem broadenedResonanceMeasure_add
    (mu nu : FiniteMeasure X) (mismatch : X -> Real)
    (hmismatch : Measurable mismatch) (T : Real) (hT : 0 < T) :
    broadenedResonanceMeasure (mu + nu) mismatch hmismatch T hT =
      broadenedResonanceMeasure mu mismatch hmismatch T hT +
        broadenedResonanceMeasure nu mismatch hmismatch T hT := by
  apply FiniteMeasure.toMeasure_injective
  change
    ((mu : Measure X) + (nu : Measure X)).withDensity
        (broadenedResonanceDensity mismatch T) =
      (mu : Measure X).withDensity
          (broadenedResonanceDensity mismatch T) +
        (nu : Measure X).withDensity
          (broadenedResonanceDensity mismatch T)
  exact withDensity_add_measure (mu : Measure X) (nu : Measure X)
    (broadenedResonanceDensity mismatch T)

variable {Omega : Type*} [MeasurableSpace Omega]

/-- At every positive time, the broadened mass of the full cluster is the
sum of the four sector broadened masses. -/
theorem DecaySectorClusterDecomposition.target_broadened_mass_eq_sectorSum
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (T : Real) (hT : 0 < T) :
    ((broadenedResonanceMeasure target id measurable_id T hT).mass : Real) =
      ((broadenedResonanceMeasure cluster.allDistinct id measurable_id
        T hT).mass : Real) +
      ((broadenedResonanceMeasure cluster.childRepeated id measurable_id
        T hT).mass : Real) +
      ((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
        T hT).mass : Real) +
      ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
        T hT).mass : Real) := by
  have htarget := congrArg
    (fun mu : FiniteMeasure Real =>
      ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real))
    cluster.target_eq_sectorSum
  calc
    ((broadenedResonanceMeasure target id measurable_id T hT).mass : Real) =
        ((broadenedResonanceMeasure
          (cluster.allDistinct + cluster.childRepeated +
            cluster.parentChildOne + cluster.parentChildTwo)
          id measurable_id T hT).mass : Real) := htarget
    _ = _ := by
      simp only [broadenedResonanceMeasure_add, FiniteMeasure.mass,
        FiniteMeasure.coeFn_add, Pi.add_apply, NNReal.coe_add]

/-- If the two main-sector broadened masses converge, the full four-sector
coefficient converges to their sum; both parent--child sectors disappear. -/
theorem DecaySectorClusterDecomposition.target_broadened_mass_tendsto_of_mainSectors
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (allDistinctLimit childRepeatedLimit : Real)
    (hall : Tendsto
      (fun n => ((broadenedResonanceMeasure cluster.allDistinct id
        measurable_id (time n) (htime_pos n)).mass : Real))
      atTop (nhds allDistinctLimit))
    (hchild : Tendsto
      (fun n => ((broadenedResonanceMeasure cluster.childRepeated id
        measurable_id (time n) (htime_pos n)).mass : Real))
      atTop (nhds childRepeatedLimit)) :
    Tendsto
      (fun n => ((broadenedResonanceMeasure target id measurable_id
        (time n) (htime_pos n)).mass : Real))
      atTop (nhds (allDistinctLimit + childRepeatedLimit)) := by
  have hparent :=
    ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay.DecaySectorClusterDecomposition.parentChild_broadened_mass_tendsto_zero
      cluster time htime_pos htime
  have hsum := (hall.add hchild).add hparent
  have htarget : Tendsto
      (fun n => ((broadenedResonanceMeasure target id measurable_id
        (time n) (htime_pos n)).mass : Real))
      atTop (nhds (allDistinctLimit + childRepeatedLimit + 0)) := by
    apply hsum.congr'
    exact Eventually.of_forall fun n => by
      symm
      dsimp only
      rw [ArchonPhysics.DecayChannelSectorClusterOnShellRecombination.DecaySectorClusterDecomposition.target_broadened_mass_eq_sectorSum
        cluster (time n) (htime_pos n)]
      ring
  simpa only [add_zero] using htarget

/-- Separate regular densities for the all-distinct and child-repeated
clusters are sufficient for a finite on-shell limit of the complete law. -/
theorem DecaySectorClusterDecomposition.target_broadened_mass_tendsto_of_mainSectorDensities
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (rhoAll rhoChild : Real -> Real)
    (hrhoAll_meas : Measurable rhoAll)
    (hrhoAll_nonneg : forall x, 0 <= rhoAll x)
    (hrhoAll_int : Integrable rhoAll)
    (hrhoAll_zero : ContinuousAt rhoAll 0)
    (hdensityAll :
      (cluster.allDistinct : Measure Real) =
        volume.withDensity (fun x => ENNReal.ofReal (rhoAll x)))
    (hrhoChild_meas : Measurable rhoChild)
    (hrhoChild_nonneg : forall x, 0 <= rhoChild x)
    (hrhoChild_int : Integrable rhoChild)
    (hrhoChild_zero : ContinuousAt rhoChild 0)
    (hdensityChild :
      (cluster.childRepeated : Measure Real) =
        volume.withDensity (fun x => ENNReal.ofReal (rhoChild x)))
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n => ((broadenedResonanceMeasure target id measurable_id
        (time n) (htime_pos n)).mass : Real))
      atTop (nhds (rhoAll 0 + rhoChild 0)) := by
  apply
    ArchonPhysics.DecayChannelSectorClusterOnShellRecombination.DecaySectorClusterDecomposition.target_broadened_mass_tendsto_of_mainSectors
      cluster time htime_pos htime (rhoAll 0) (rhoChild 0)
  · exact broadenedResonanceMeasure_id_mass_tendsto_of_density
      cluster.allDistinct rhoAll hrhoAll_meas hrhoAll_nonneg hrhoAll_int
      hrhoAll_zero hdensityAll time htime_pos htime
  · exact broadenedResonanceMeasure_id_mass_tendsto_of_density
      cluster.childRepeated rhoChild hrhoChild_meas hrhoChild_nonneg
      hrhoChild_int hrhoChild_zero hdensityChild time htime_pos htime

end

end ArchonPhysics.DecayChannelSectorClusterOnShellRecombination
