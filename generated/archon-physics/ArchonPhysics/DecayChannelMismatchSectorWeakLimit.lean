import ArchonPhysics.CanonicalCollisionMeasureWeakLimit
import ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull

/-!
# Decay-channel mismatch sector weak limits

The exact four-way mode-equality partition is lifted here from raw measures
to the canonical per-site finite measures used by the thermodynamic collision
limit.  Addition is continuous for the weak topology on finite measures, so
sectorwise weak limits recombine to the full collision limit.

The two parent--child repeated sectors require no further analytic input:
their already proved uniform quadratic small-ball estimates force every weak
limit to give zero mass to exact resonance.  Thus, after this bridge, the only
sector-specific zero-atom inputs are the all-distinct and child-repeated
sectors.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.DecayChannelMismatchSectorWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrozenCollisionPerSiteNormalization
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- One predicate-restricted decay-channel sector with the same canonical
per-site normalization and volume convention as
`canonicalCollisionPerSiteFiniteMeasure`. -/
def canonicalDecaySectorPerSiteMismatchFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (keep : {N : Nat} -> [NeZero N] -> OrderedModeTriple N -> Prop)
    (n : Nat) (omega : Omega) : FiniteMeasure Real :=
  perSitePositiveWeightedMismatchFiniteMeasureWhere
    (ensemble.restrictPositiveMass (N := n + 2) omega)
    decayInteractionSign (keep (N := n + 2))

/-- The full canonical decay-channel mismatch measure is exactly the sum of
the four disjoint mode-equality sectors at every finite volume. -/
theorem canonicalCollisionPerSiteFiniteMeasure_decay_eq_sectorSum
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega) :
    canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega =
      canonicalDecaySectorPerSiteMismatchFiniteMeasure
          ensemble (fun {_N} _inst => AllDistinctModes) n omega +
        canonicalDecaySectorPerSiteMismatchFiniteMeasure
          ensemble (fun {_N} _inst => ChildRepeated) n omega +
        canonicalDecaySectorPerSiteMismatchFiniteMeasure
          ensemble (fun {_N} _inst => ParentChildOneRepeated) n omega +
        canonicalDecaySectorPerSiteMismatchFiniteMeasure
          ensemble (fun {_N} _inst => ParentChildTwoRepeated) n omega := by
  apply FiniteMeasure.toMeasure_injective
  unfold canonicalCollisionPerSiteFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasure
    canonicalDecaySectorPerSiteMismatchFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  simp only [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_add]
  change
    ((n + 2 : Nat) : NNReal)⁻¹ •
        positiveWeightedMismatchMeasure
          (ensemble.restrictPositiveMass (N := n + 2) omega)
          decayInteractionSign =
      ((n + 2 : Nat) : NNReal)⁻¹ •
          positiveWeightedMismatchMeasureWhere
            (ensemble.restrictPositiveMass (N := n + 2) omega)
            decayInteractionSign AllDistinctModes +
        ((n + 2 : Nat) : NNReal)⁻¹ •
          positiveWeightedMismatchMeasureWhere
            (ensemble.restrictPositiveMass (N := n + 2) omega)
            decayInteractionSign ChildRepeated +
        ((n + 2 : Nat) : NNReal)⁻¹ •
          positiveWeightedMismatchMeasureWhere
            (ensemble.restrictPositiveMass (N := n + 2) omega)
            decayInteractionSign ParentChildOneRepeated +
        ((n + 2 : Nat) : NNReal)⁻¹ •
          positiveWeightedMismatchMeasureWhere
            (ensemble.restrictPositiveMass (N := n + 2) omega)
            decayInteractionSign ParentChildTwoRepeated
  rw [positiveWeightedMismatchMeasure_eq_modeEqualityPartition,
    smul_add, smul_add, smul_add]

/-- Weak convergence of all four sectors recombines into weak convergence of
the full canonical decay-channel measure. -/
theorem canonicalCollisionPerSiteFiniteMeasure_decay_tendsto_of_sector_tendsto
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (allDistinct childRepeated parentChildOne parentChildTwo :
      FiniteMeasure Real)
    (hall : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => AllDistinctModes) · omega)
      atTop (nhds allDistinct))
    (hchild : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) · omega)
      atTop (nhds childRepeated))
    (hone : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) · omega)
      atTop (nhds parentChildOne))
    (htwo : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) · omega)
      atTop (nhds parentChildTwo)) :
    Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega)
      atTop
      (nhds (allDistinct + childRepeated + parentChildOne + parentChildTwo)) := by
  have hsum := ((hall.add hchild).add hone).add htwo
  apply hsum.congr'
  exact Eventually.of_forall fun n =>
    (canonicalCollisionPerSiteFiniteMeasure_decay_eq_sectorSum
      ensemble n omega).symm

/-- A finite sum of sector limits is exact-resonance-null when each summand
is. -/
theorem sectorSum_singleton_zero_eq_zero
    (allDistinct childRepeated parentChildOne parentChildTwo :
      FiniteMeasure Real)
    (hall : (allDistinct : Measure Real) ({0} : Set Real) = 0)
    (hchild : (childRepeated : Measure Real) ({0} : Set Real) = 0)
    (hone : (parentChildOne : Measure Real) ({0} : Set Real) = 0)
    (htwo : (parentChildTwo : Measure Real) ({0} : Set Real) = 0) :
    ((allDistinct + childRepeated + parentChildOne + parentChildTwo :
      FiniteMeasure Real) : Measure Real) ({0} : Set Real) = 0 := by
  simp [Measure.add_apply, hall, hchild, hone, htwo]

/-- The canonical sector convention at physical volume `n + 2` is the
one-step tail of the previously defined first parent--child source. -/
theorem canonicalDecaySector_parentChildOne_eq_iid_tail
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega) (n : Nat) :
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) n omega =
      iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (n + 1) := by
  rfl

/-- The analogous exact index bridge for the second parent--child sector. -/
theorem canonicalDecaySector_parentChildTwo_eq_iid_tail
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega) (n : Nat) :
    canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) n omega =
      iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (n + 1) := by
  rfl

/-- The two repeated parent--child zero-atom conclusions are discharged
automatically.  Consequently all-distinct and child-repeated are the only
zero-atom premises needed for the recombined sector limit. -/
theorem sectorSum_singleton_zero_eq_zero_of_allDistinct_of_childRepeated
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (allDistinct childRepeated parentChildOne parentChildTwo :
      FiniteMeasure Real)
    (hallLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => AllDistinctModes) · omega)
      atTop (nhds allDistinct))
    (hchildLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) · omega)
      atTop (nhds childRepeated))
    (honeLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) · omega)
      atTop (nhds parentChildOne))
    (htwoLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) · omega)
      atTop (nhds parentChildTwo))
    (hallZero : (allDistinct : Measure Real) ({0} : Set Real) = 0)
    (hchildZero : (childRepeated : Measure Real) ({0} : Set Real) = 0) :
    ((allDistinct + childRepeated + parentChildOne + parentChildTwo :
      FiniteMeasure Real) : Measure Real) ({0} : Set Real) = 0 := by
  have honeTail : Tendsto
      (fun n => iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (n + 1))
      atTop (nhds parentChildOne) := by
    simpa only [canonicalDecaySector_parentChildOne_eq_iid_tail] using honeLimit
  have honeFull : Tendsto
      (iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
      atTop (nhds parentChildOne) :=
    (tendsto_add_atTop_iff_nat 1).mp honeTail
  have htwoTail : Tendsto
      (fun n => iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (n + 1))
      atTop (nhds parentChildTwo) := by
    simpa only [canonicalDecaySector_parentChildTwo_eq_iid_tail] using htwoLimit
  have htwoFull : Tendsto
      (iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
      atTop (nhds parentChildTwo) :=
    (tendsto_add_atTop_iff_nat 1).mp htwoTail
  exact sectorSum_singleton_zero_eq_zero
    allDistinct childRepeated parentChildOne parentChildTwo
    hallZero hchildZero
    (iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_weakLimit_zeroAtom
      ensemble omega parentChildOne honeFull)
    (iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_weakLimit_zeroAtom
      ensemble omega parentChildTwo htwoFull)

/-- End-to-end sector criterion for a supplied full thermodynamic collision
limit.  Uniqueness of weak limits identifies it with the four-sector sum,
after which the repeated parent--child sectors vanish at exact resonance. -/
theorem fullLimit_singleton_zero_eq_zero_of_sector_limits
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target allDistinct childRepeated parentChildOne parentChildTwo :
      FiniteMeasure Real)
    (hfull : Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure
        ensemble decayInteractionSign n omega)
      atTop (nhds target))
    (hallLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => AllDistinctModes) · omega)
      atTop (nhds allDistinct))
    (hchildLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ChildRepeated) · omega)
      atTop (nhds childRepeated))
    (honeLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildOneRepeated) · omega)
      atTop (nhds parentChildOne))
    (htwoLimit : Tendsto
      (canonicalDecaySectorPerSiteMismatchFiniteMeasure ensemble
        (fun {_N} _inst => ParentChildTwoRepeated) · omega)
      atTop (nhds parentChildTwo))
    (hallZero : (allDistinct : Measure Real) ({0} : Set Real) = 0)
    (hchildZero : (childRepeated : Measure Real) ({0} : Set Real) = 0) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  have hsector :=
    canonicalCollisionPerSiteFiniteMeasure_decay_tendsto_of_sector_tendsto
      ensemble omega allDistinct childRepeated parentChildOne parentChildTwo
      hallLimit hchildLimit honeLimit htwoLimit
  have htarget : target =
      allDistinct + childRepeated + parentChildOne + parentChildTwo :=
    tendsto_nhds_unique hfull hsector
  rw [htarget]
  exact sectorSum_singleton_zero_eq_zero_of_allDistinct_of_childRepeated
    ensemble omega allDistinct childRepeated parentChildOne parentChildTwo
    hallLimit hchildLimit honeLimit htwoLimit hallZero hchildZero

end

end ArchonPhysics.DecayChannelMismatchSectorWeakLimit
