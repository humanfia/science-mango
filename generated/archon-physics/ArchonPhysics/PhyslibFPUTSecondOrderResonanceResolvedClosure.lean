import ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration

/-!
# Full second-order resonance-resolved FPUT closure

The q-level second-order identity is rewritten so that its three transparent
corrections are separated into genuinely potentially resonant sectors and
algebraically off-resonant sectors.  The dangerous sectors remain in the
exact main formula and are explicitly subtracted before any error estimate.

The cross-orbit contribution is composed through an abstract bound parameter.
The current concrete endpoint instantiates it with the committed `N^2 / T`
bound; a later linear-volume cross theorem can replace only that interface.
No displayed constant is asserted to be uniform in the lattice size.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

/-! ## Exact full second-order formula -/

/-- Exact resonance-resolved full second-order formula.  Potentially resonant
corrections are retained as a main contribution, not treated as error. -/
theorem normalizedSecondOrderHaarBroadening_eq_resonanceResolvedClosure
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time =
      qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed +
        allEqualOrbitGainSum m kappa time energy observed +
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        qLevelOffResonantCorrectionSum
          m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed := by
  have hOld := normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
    m kappa beta energy observed htime hObserved hEnergy
  have hCorrections := qLevelThreeCorrections_eq_potential_add_offResonant
    m kappa time energy observed
  rw [hOld]
  linear_combination hCorrections

/-! ## Cross-bound interface -/

/-- Current committed cross-orbit interface.  This intentionally records the
`N^2 / T` bound and can later be replaced by a linear-volume implementation. -/
def currentSecondOrderCrossOrbitFiniteVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa energyBound time : Real)
    (observed : Lattice.Site N) : Real :=
  2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
    (modeFrequency m observed * time)

/-- The existing q-level cross estimate realizes the current interface. -/
theorem abs_secondOrderCrossOrbitRemainder_le_currentFiniteVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real) (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |secondOrderCrossOrbitRemainder
        m kappa time energy observed| ≤
      currentSecondOrderCrossOrbitFiniteVolumeBound
        m kappa energyBound time observed := by
  exact abs_qLevelCrossOrbitRemainder_le_energyVolume
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

/-! ## Residual estimate with a replaceable cross bound -/

/-- Abstract composition theorem.  Once a cross-orbit estimate is supplied,
the residual after subtracting the q-level main, all-equal orbit gain, and
dangerous corrections is bounded by the off-resonant, counterrotating, and
cross pieces. -/
theorem abs_resonanceResolvedResidual_le_of_crossBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time crossBound : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hCross : |secondOrderCrossOrbitRemainder
      m kappa time energy observed| ≤ crossBound) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy observed time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed -
        allEqualOrbitGainSum m kappa time energy observed -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed| ≤
      qLevelOffResonantCorrectionStaticMass
          m kappa energy observed / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
          ((2 / modeFrequency m observed) ^ 2 / time) +
        crossBound := by
  have hExact :=
    normalizedSecondOrderHaarBroadening_eq_resonanceResolvedClosure
      m kappa beta energy observed htime hObserved hEnergy
  have hOff := abs_qLevelOffResonantCorrectionSum_le_inverseTime
    m kappa energy observed htime hObserved
  have hCounter := abs_qLevelCounterrotatingRemainder_le_inverseTime
    m kappa energy observed htime hObserved hEnergy
  have hResidual :
      normalizedSecondOrderHaarBroadening
            m kappa beta energy observed time -
          qLevelResolvedSecondOrderSignedFluxMain
            m kappa time energy observed -
          allEqualOrbitGainSum m kappa time energy observed -
          qLevelPotentiallyResonantCorrectionSum
            m kappa time energy observed =
        qLevelOffResonantCorrectionSum
            m kappa time energy observed +
          secondOrderCounterrotatingRemainder
            m kappa time energy observed +
          secondOrderCrossOrbitRemainder
            m kappa time energy observed := by
    rw [hExact]
    ring
  rw [hResidual]
  calc
    |qLevelOffResonantCorrectionSum
          m kappa time energy observed +
        secondOrderCounterrotatingRemainder
          m kappa time energy observed +
        secondOrderCrossOrbitRemainder
          m kappa time energy observed| ≤
      |qLevelOffResonantCorrectionSum
          m kappa time energy observed| +
        |secondOrderCounterrotatingRemainder
          m kappa time energy observed| +
        |secondOrderCrossOrbitRemainder
          m kappa time energy observed| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ qLevelOffResonantCorrectionStaticMass
          m kappa energy observed / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
          ((2 / modeFrequency m observed) ^ 2 / time) +
        crossBound := by
      exact add_le_add (add_le_add hOff hCounter) hCross

/-- Current total fixed-volume residual interface: off-resonant corrections,
counterrotating remainder, and the committed quadratic-volume cross bound. -/
def currentResonanceResolvedResidualBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound time : Real) : Real :=
  qLevelOffResonantCorrectionStaticMass
      m kappa energy observed / time +
    allDistinctCounterrotatingStaticFluxMass
      m kappa energy observed *
      ((2 / modeFrequency m observed) ^ 2 / time) +
    currentSecondOrderCrossOrbitFiniteVolumeBound
      m kappa energyBound time observed

/-- Concrete fixed-volume total error bound using the currently committed
`N^2 / T` cross estimate.  The dangerous correction sector is subtracted and
does not occur on the error side. -/
theorem abs_resonanceResolvedResidual_le_currentFiniteVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real) (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy observed time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy observed -
        allEqualOrbitGainSum m kappa time energy observed -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed| ≤
      currentResonanceResolvedResidualBound
        m kappa energy observed energyBound time := by
  apply abs_resonanceResolvedResidual_le_of_crossBound
    m kappa beta energy observed htime hObserved hEnergy
  exact abs_secondOrderCrossOrbitRemainder_le_currentFiniteVolumeBound
    m kappa energy observed energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime hObserved

end

end ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedClosure
