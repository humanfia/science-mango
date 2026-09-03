import ArchonPhysics.ActualFPUTR1FirstDefectEndpointBondSourceAdapter

/-!
# Actual punctured-evaluator endpoint bond-source constructor

This companion module constructs the endpoint physical-bond certificate from
the literal punctured flower evaluator.  The root view stores only data:
arity, coupling, ordered child modes, child coordinates, and their continuity.
The root-integral identity is proved separately by dependent case analysis on
all five non-`flower` constructors, so no renamed equality premise is hidden in
the provenance record.

This closes root opening and physical-bond synthesis for every endpoint in an
already constructed first-defect readback.  Constructing that classifier and
proving continuity of a model-specific injected boundary remain upstream
obligations.  No hard-band, probabilistic, or kinetic estimate is asserted.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualFPUTR1FirstDefectEndpointBondSourceAdapter

set_option autoImplicit false

open ArchonPhysics.ActualFPUTEndpointFirstDefectSecondMoment
open ArchonPhysics.ActualFPUTEndpointFirstDefectSecondMoment.ActualFPUTEndpointFirstDefectCoherentReadback
open ArchonPhysics.ActualFPUTMarkedFlowerCoupleReadback
open ArchonPhysics.ActualFPUTPuncturedFlowerEvaluatorReadback
open ArchonPhysics.ActualFPUTR1FirstDefectPhysicalSourceGramBridge
open ArchonPhysics.ActualFPUTR1PhysicalSourceBondReadback
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibFPUTActualMixedTreeRawHistoryExpansion
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Root data recovered definitionally from a literal punctured endpoint. -/
structure ActualFPUTPuncturedEndpointRawRoot
    (m : PositiveMassConfig N) (kappa beta : Real)
    (radius : Site N → Real) (boundary : Site N → Real → Complex)
    (phase : UnitAddTorus (Site N))
    (endpoint : ActualFPUTRawFlowerEndpoint N) where
  arity : Nat
  coupling : Real
  modes : Fin arity → Site N
  childCoordinate : Fin arity → Real → Complex
  childCoordinate_continuous : ∀ slot, Continuous (childCoordinate slot)

/-- The literal evaluator itself constructs its root provenance. -/
def actualFPUTPuncturedEndpointRawRoot
    (m : PositiveMassConfig N) (kappa beta : Real)
    (radius : Site N → Real) (boundary : Site N → Real → Complex)
    (hboundary : ∀ mode, Continuous (boundary mode))
    (phase : UnitAddTorus (Site N))
    (endpoint : ActualFPUTRawFlowerEndpoint N) :
    ActualFPUTPuncturedEndpointRawRoot m kappa beta radius boundary phase endpoint := by
  rcases endpoint with ⟨tree, outputMode, history⟩
  cases tree with
  | flower =>
      refine
        { arity := 0
          coupling := 0
          modes := Fin.elim0
          childCoordinate := Fin.elim0
          childCoordinate_continuous := ?_ }
      intro slot
      exact Fin.elim0 slot
  | q1Left stem right =>
      rcases history with ⟨modes, stemHistory, rightHistory⟩
      refine
        { arity := 2
          coupling := kappa
          modes := modes
          childCoordinate := ![
            actualFPUTPuncturedRawFlowerCoordinateContribution
              m kappa beta radius phase boundary stem
                (modes 0) stemHistory,
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase right
                (modes 1) rightHistory]
          childCoordinate_continuous := ?_ }
      intro slot
      fin_cases slot
      · exact continuous_actualFPUTPuncturedRawFlowerCoordinateContribution
          m kappa beta radius phase boundary hboundary stem
            (modes 0) stemHistory
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase right (modes 1) rightHistory
  | q1Right left stem =>
      rcases history with ⟨modes, leftHistory, stemHistory⟩
      refine
        { arity := 2
          coupling := kappa
          modes := modes
          childCoordinate := ![
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase left
                (modes 0) leftHistory,
            actualFPUTPuncturedRawFlowerCoordinateContribution
              m kappa beta radius phase boundary stem
                (modes 1) stemHistory]
          childCoordinate_continuous := ?_ }
      intro slot
      fin_cases slot
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase left (modes 0) leftHistory
      · exact continuous_actualFPUTPuncturedRawFlowerCoordinateContribution
          m kappa beta radius phase boundary hboundary stem
            (modes 1) stemHistory
  | q2First stem second third =>
      rcases history with ⟨modes, stemHistory, secondHistory, thirdHistory⟩
      refine
        { arity := 3
          coupling := beta
          modes := modes
          childCoordinate := ![
            actualFPUTPuncturedRawFlowerCoordinateContribution
              m kappa beta radius phase boundary stem
                (modes 0) stemHistory,
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase second
                (modes 1) secondHistory,
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase third
                (modes 2) thirdHistory]
          childCoordinate_continuous := ?_ }
      intro slot
      fin_cases slot
      · exact continuous_actualFPUTPuncturedRawFlowerCoordinateContribution
          m kappa beta radius phase boundary hboundary stem
            (modes 0) stemHistory
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase second (modes 1) secondHistory
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase third (modes 2) thirdHistory
  | q2Second first stem third =>
      rcases history with ⟨modes, firstHistory, stemHistory, thirdHistory⟩
      refine
        { arity := 3
          coupling := beta
          modes := modes
          childCoordinate := ![
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase first
                (modes 0) firstHistory,
            actualFPUTPuncturedRawFlowerCoordinateContribution
              m kappa beta radius phase boundary stem
                (modes 1) stemHistory,
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase third
                (modes 2) thirdHistory]
          childCoordinate_continuous := ?_ }
      intro slot
      fin_cases slot
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase first (modes 0) firstHistory
      · exact continuous_actualFPUTPuncturedRawFlowerCoordinateContribution
          m kappa beta radius phase boundary hboundary stem
            (modes 1) stemHistory
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase third (modes 2) thirdHistory
  | q2Third first second stem =>
      rcases history with ⟨modes, firstHistory, secondHistory, stemHistory⟩
      refine
        { arity := 3
          coupling := beta
          modes := modes
          childCoordinate := ![
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase first
                (modes 0) firstHistory,
            actualFPUTMixedRawCoordinateContribution
              m kappa beta radius phase second
                (modes 1) secondHistory,
            actualFPUTPuncturedRawFlowerCoordinateContribution
              m kappa beta radius phase boundary stem
                (modes 2) stemHistory]
          childCoordinate_continuous := ?_ }
      intro slot
      fin_cases slot
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase first (modes 0) firstHistory
      · exact continuous_actualFPUTMixedRawCoordinateContribution
          m kappa beta radius phase second (modes 1) secondHistory
      · exact continuous_actualFPUTPuncturedRawFlowerCoordinateContribution
          m kappa beta radius phase boundary hboundary stem
            (modes 2) stemHistory

/-- Opening the root recorded above is a theorem of the punctured evaluator,
not a field of the provenance record. -/
theorem actualFPUTPuncturedEndpointRawRoot_contribution_eq
    (m : PositiveMassConfig N) (kappa beta : Real)
    (radius : Site N → Real) (boundary : Site N → Real → Complex)
    (hboundary : ∀ mode, Continuous (boundary mode))
    (phase : UnitAddTorus (Site N))
    (endpoint : ActualFPUTRawFlowerEndpoint N)
    (hnonflower : endpoint.flowerTree ≠ .flower) (time : Real) :
    let root := actualFPUTPuncturedEndpointRawRoot
      m kappa beta radius boundary hboundary phase endpoint
    actualFPUTPuncturedRawFlowerEndpointContribution
        m kappa beta radius phase boundary endpoint.flowerTree
          endpoint.outputMode endpoint.historySkeleton time =
      ∫ sourceTime in (0 : Real)..time,
        actualFPUTRawVertexRotatedSource m root.coupling endpoint.outputMode
          root.modes (fun slot ↦ root.childCoordinate slot sourceTime)
          sourceTime := by
  rcases endpoint with ⟨tree, outputMode, history⟩
  cases tree with
  | flower =>
      exact (hnonflower rfl).elim
  | q1Left stem right =>
      rcases history with ⟨modes, stemHistory, rightHistory⟩
      rfl
  | q1Right left stem =>
      rcases history with ⟨modes, leftHistory, stemHistory⟩
      rfl
  | q2First stem second third =>
      rcases history with ⟨modes, stemHistory, secondHistory, thirdHistory⟩
      rfl
  | q2Second first stem third =>
      rcases history with ⟨modes, firstHistory, stemHistory, thirdHistory⟩
      rfl
  | q2Third first second stem =>
      rcases history with ⟨modes, firstHistory, secondHistory, stemHistory⟩
      rfl

theorem continuous_actualFPUTRawVertexPhysicalBondSource
    {arity : Nat} (m : PositiveMassConfig N) (coupling : Real)
    (observed : Site N) (modes : Fin arity → Site N)
    (childCoordinate : Fin arity → Real → Complex)
    (hchild : ∀ slot, Continuous (childCoordinate slot))
    (bond : Site N) :
    Continuous (fun time ↦
      actualFPUTRawVertexPhysicalBondSource m coupling observed modes
        (fun slot ↦ childCoordinate slot time) time bond) := by
  classical
  have hphase : Continuous (fun time : Real ↦
      phaseFactor (modeFrequency m observed * time)) :=
    continuous_phaseFactor_real.comp (by fun_prop)
  have hprod : Continuous (fun time : Real ↦
      ∏ slot, childCoordinate slot time) := by
    exact continuous_finsetProd Finset.univ (fun slot _ ↦ hchild slot)
  unfold actualFPUTRawVertexPhysicalBondSource
  exact (((hphase.mul continuous_const).mul continuous_const).mul hprod)

variable {terms : Finset (ActualFPUTRawFlowerEndpoint N)}
variable {HasActualSideTaggedCanonicalFirstHit :
  ActualFPUTRawFlowerEndpoint N → ActualFPUTRawFlowerEndpoint N → Prop}

namespace ActualFPUTR1FirstDefectEndpointPhysicalBondSourceCertificate

/-- Construct the endpoint bond-source certificate from the actual punctured
evaluator.  The only extra input is continuity of the injected boundary
history; both source equalities are consequences of one recovered raw root. -/
def ofActualPuncturedEvaluator
    (readback : ActualFPUTEndpointFirstDefectCoherentReadback terms
      HasActualSideTaggedCanonicalFirstHit)
    (rowWeight : Site N → Complex)
    (m : PositiveMassConfig N) (kappa beta g : Real)
    (radius : Site N → Real) (boundary : Site N → Real → Complex)
    (hboundary : ∀ mode, Continuous (boundary mode))
    (phase : UnitAddTorus (Site N)) :
    ActualFPUTR1FirstDefectEndpointPhysicalBondSourceCertificate
      readback rowWeight m kappa beta g radius boundary phase := by
  let root := fun endpoint : ActualFPUTR1FirstDefectEndpointOccurrence readback ↦
    actualFPUTPuncturedEndpointRawRoot m kappa beta radius boundary hboundary
      phase endpoint.1
  let weight := fun endpoint : ActualFPUTR1FirstDefectEndpointOccurrence readback ↦
    rowWeight endpoint.1.outputMode * (g : Complex) ^ endpoint.1.couplingOrder
  refine
    { endpointPhysicalBondSourceAt := fun time endpoint ↦
        if endpoint.1.flowerTree = .flower then 0 else
          fun bond ↦ weight endpoint *
            ∫ sourceTime in (0 : Real)..time,
              actualFPUTRawVertexPhysicalBondSource m (root endpoint).coupling
                endpoint.1.outputMode (root endpoint).modes
                (fun slot ↦ (root endpoint).childCoordinate slot sourceTime)
                sourceTime bond
      rawArity := fun endpoint ↦ (root endpoint).arity
      rawCoupling := fun endpoint ↦ (root endpoint).coupling
      rawModes := fun endpoint ↦ (root endpoint).modes
      rawChildCoordinate := fun endpoint ↦ (root endpoint).childCoordinate
      rawWeight := weight
      nonflower_endpointAction_eq_rawRootIntegral := ?_
      nonflower_raw_source_eq := ?_
      nonflower_raw_bond_intervalIntegrable := ?_
      flower_source_eq_zero := ?_ }
  · intro time endpoint hnonflower
    unfold actualFPUTR1FirstDefectEndpointActionAt
      actualFPUTSelectedRowFlowerTerm
      actualFPUTRawFlowerEndpointPuncturedAmplitude
    rw [actualFPUTPuncturedEndpointRawRoot_contribution_eq
      m kappa beta radius boundary hboundary phase endpoint.1
        hnonflower time]
    simp only [weight]
    ring
  · intro time endpoint hnonflower bond
    simp only [hnonflower, ↓reduceIte]
  · intro time endpoint _hnonflower bond
    apply Continuous.intervalIntegrable
    apply continuous_actualFPUTRawVertexPhysicalBondSource
    exact (root endpoint).childCoordinate_continuous
  · intro time endpoint hflower
    simp only [hflower, ↓reduceIte]

end ActualFPUTR1FirstDefectEndpointPhysicalBondSourceCertificate

end

end ArchonPhysics.ActualFPUTR1FirstDefectEndpointBondSourceAdapter
