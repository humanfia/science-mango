import ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
import ArchonPhysics.HarmonicNormalizedEdgeFrame

/-!
# Observable and derivative bridge for canonical iid signed modes

This module proves two concrete facts about the observable defined in
`CanonicalIIDCoerciveSignedModalHierarchy`:

1. every signed ordered-mode amplitude, and every arbitrary finite block of
   them, is jointly measurable in the canonical iid sample and time;
2. on a genuine coercive Hamilton orbit the measurable signed eigenvector
   obeys the exact forced-oscillator equation and hence the exact
   interaction-picture source equation.

The source is the full nonlinear mass-weighted force projected into the
first-positive-pivot eigenvector; it includes both alpha and beta pieces.
No derivative is yet moved through the continuous probability integral.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

theorem measurable_canonicalMass_coordinate (i : Lattice.Site N) :
    Measurable fun omega : CanonicalSample =>
      (canonicalMass (N := N) omega).mass i := by
  exact measurable_restrictPositiveMass_coordinate
    canonicalIIDMassPhaseEnsemble i

theorem measurable_canonicalOrderedFrequency (k : OrderedModeIndex N) :
    Measurable (canonicalOrderedFrequency (N := N) k) := by
  have h := measurable_harmonicOrderedModeFrequencies_unconditional
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble)
  exact (measurable_pi_apply k).comp h

theorem measurable_canonicalOrderedModalPosition
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable (canonicalOrderedModalPosition (N := N)
      kappa beta g hbeta a k) := by
  let massST : CanonicalSample × Real → Lattice.PositiveMassConfig N :=
    fun st => canonicalMass (N := N) st.1
  let weighted : CanonicalSample × Real → WeightedConfiguration N :=
    massWeightedPositionSample massST
      (canonicalFlowPosition (N := N) kappa beta g hbeta a)
  have hmass : ∀ i, Measurable fun st => (massST st).mass i :=
    fun i => (measurable_canonicalMass_coordinate (N := N) i).comp measurable_fst
  have hweighted : Measurable weighted :=
    measurable_massWeightedPositionSample massST
      (canonicalFlowPosition (N := N) kappa beta g hbeta a)
      hmass (measurable_canonicalFlowPosition
        (N := N) kappa beta g hbeta a)
  unfold canonicalOrderedModalPosition dotProduct
  apply Finset.measurable_sum
  intro i _hi
  exact ((measurable_pi_apply i).comp
      ((measurable_orderedEigenvectorSample
        canonicalIIDMassPhaseEnsemble k).comp measurable_fst)).mul
    ((measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hweighted))

theorem measurable_canonicalOrderedModalMomentum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable (canonicalOrderedModalMomentum (N := N)
      kappa beta g hbeta a k) := by
  let massST : CanonicalSample × Real → Lattice.PositiveMassConfig N :=
    fun st => canonicalMass (N := N) st.1
  let weighted : CanonicalSample × Real → WeightedConfiguration N :=
    massWeightedMomentumSample massST
      (canonicalFlowMomentum (N := N) kappa beta g hbeta a)
  have hmass : ∀ i, Measurable fun st => (massST st).mass i :=
    fun i => (measurable_canonicalMass_coordinate (N := N) i).comp measurable_fst
  have hweighted : Measurable weighted :=
    measurable_massWeightedMomentumSample massST
      (canonicalFlowMomentum (N := N) kappa beta g hbeta a)
      hmass (measurable_canonicalFlowMomentum
        (N := N) kappa beta g hbeta a)
  unfold canonicalOrderedModalMomentum dotProduct
  apply Finset.measurable_sum
  intro i _hi
  exact ((measurable_pi_apply i).comp
      ((measurable_orderedEigenvectorSample
        canonicalIIDMassPhaseEnsemble k).comp measurable_fst)).mul
    ((measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hweighted))

theorem measurable_canonicalInteractionAmplitude
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable (canonicalInteractionAmplitude (N := N)
      kappa beta g hbeta a k) := by
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) k st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) k).comp measurable_fst
  have hQ := measurable_canonicalOrderedModalPosition
    (N := N) kappa beta g hbeta a k
  have hP := measurable_canonicalOrderedModalMomentum
    (N := N) kappa beta g hbeta a k
  unfold canonicalInteractionAmplitude phaseRenormalize phaseFactor
    complexModeAmplitude
  fun_prop

theorem measurable_canonicalSignedInteractionAmplitude
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable (canonicalSignedInteractionAmplitude (N := N)
      kappa beta g hbeta a entry) := by
  rcases entry with ⟨sign, k⟩
  have h := measurable_canonicalInteractionAmplitude
    (N := N) kappa beta g hbeta a k
  cases sign with
  | phase =>
      change Measurable (canonicalInteractionAmplitude (N := N) kappa beta g hbeta a k)
      exact h
  | conjugate =>
      change Measurable fun st => star
        (canonicalInteractionAmplitude (N := N) kappa beta g hbeta a k st)
      exact Complex.continuous_conj.measurable.comp h

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Arbitrary finite signed block on the genuine canonical random flow. -/
def canonicalSignedBlockObservable
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (st : CanonicalSample × Real) : Complex :=
  ∏ i ∈ block,
    canonicalSignedInteractionAmplitude (N := N)
      kappa beta g hbeta a (entry i) st

theorem measurable_canonicalSignedBlockObservable
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    Measurable (canonicalSignedBlockObservable (N := N)
      kappa beta g hbeta a entry block) := by
  unfold canonicalSignedBlockObservable
  apply Finset.measurable_prod
  intro i _hi
  exact measurable_canonicalSignedInteractionAmplitude
    (N := N) kappa beta g hbeta a (entry i)

theorem measurable_canonicalSignedBlockObservable_fixedTime
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, time) := by
  exact (measurable_canonicalSignedBlockObservable
    (N := N) kappa beta g hbeta a entry block).comp
      (measurable_id.prodMk measurable_const)

/-! ## Exact signed-frame modal equation on a genuine Hamilton orbit -/

/-- Coordinate in the explicit measurable signed ordered eigenvector. -/
def orderedSignedCoordinate
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (x : WeightedConfiguration N) : Real :=
  signedOrderedEigenvector (harmonicHermitian m) k ⬝ᵥ x

/-- The same signed ordered coordinate as a continuous linear functional. -/
def orderedSignedCoordinateCLM
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) :
    WeightedConfiguration N →L[Real] Real :=
  ∑ i : Lattice.Site N,
    signedOrderedEigenvector (harmonicHermitian m) k i •
      PiLp.proj 2 (fun _ : Lattice.Site N => Real) i

@[simp] theorem orderedSignedCoordinateCLM_apply
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (x : WeightedConfiguration N) :
    orderedSignedCoordinateCLM m k x = orderedSignedCoordinate m k x := by
  classical
  simp [orderedSignedCoordinateCLM, orderedSignedCoordinate, dotProduct]

/-- The true nonlinear mass-weighted force projected into that frame. -/
def orderedSignedNonlinearForce
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : OrderedModeIndex N) (q : HilbertConfiguration N) : Real :=
  orderedSignedCoordinate m k
    (transformedNonlinearForce m kappa beta g q)

/-- Interaction-picture source of the signed-frame ordered mode. -/
def orderedSignedRotatedSource
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : OrderedModeIndex N) (q : Real → HilbertConfiguration N)
    (time : Real) : Complex :=
  phaseFactor (orderedModeFrequency (harmonicHermitian m) k * time) *
    forcedModeSource (orderedModeFrequency (harmonicHermitian m) k)
      (orderedSignedNonlinearForce m kappa beta g k (q time))

omit [Fintype I] [DecidableEq I] in
theorem hasDerivAt_orderedSignedCoordinate
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    {x : Real → WeightedConfiguration N} {x' : WeightedConfiguration N}
    {time : Real} (hx : HasMassWeightedDerivAt x x' time) :
    HasDerivAt (fun s => orderedSignedCoordinate m k (x s))
      (orderedSignedCoordinate m k x') time := by
  simp only [HasMassWeightedDerivAt] at hx
  simpa only [Function.comp_def, orderedSignedCoordinateCLM_apply] using
    (orderedSignedCoordinateCLM m k).hasFDerivAt.comp_hasDerivAt time hx

omit [Fintype I] [DecidableEq I] in
theorem orderedSignedCoordinate_harmonicOperator
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) (x : WeightedConfiguration N) :
    orderedSignedCoordinate m k (harmonicOperator m x) =
      orderedEigenvalue (harmonicHermitian m) k *
        orderedSignedCoordinate m k x := by
  let v := signedOrderedEigenvector (harmonicHermitian m) k
  have hv := signedOrderedEigenvector_eigenvector
    (harmonicHermitian m) hsimple k
  have htranspose :
      (matrixVal (harmonicHermitian m))ᵀ =
        matrixVal (harmonicHermitian m) := by
    have hH : (matrixVal (harmonicHermitian m)).IsHermitian :=
      (harmonicHermitian m).2
    ext i j
    have hij := congrArg
      (fun M : Matrix (Lattice.Site N) (Lattice.Site N) Real => M i j) hH
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hij
  change v ⬝ᵥ
      (matrixVal (harmonicHermitian m) *ᵥ (WithLp.ofLp x)) =
    orderedEigenvalue (harmonicHermitian m) k *
      (v ⬝ᵥ (WithLp.ofLp x))
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, htranspose, hv]
  simpa [v, smul_eq_mul] using
    (Matrix.smul_dotProduct (orderedEigenvalue (harmonicHermitian m) k)
      (signedOrderedEigenvector (harmonicHermitian m) k) (WithLp.ofLp x))

/-- Position and momentum paths in the explicit signed ordered frame. -/
def orderedSignedPositionPath
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (q : Real → HilbertConfiguration N) : Real → Real :=
  fun time => orderedSignedCoordinate m k (massWeightedPosition m q time)

def orderedSignedMomentumPath
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (p : Real → HilbertConfiguration N) : Real → Real :=
  fun time => orderedSignedCoordinate m k (massWeightedMomentum m p time)

omit [Fintype I] [DecidableEq I] in
theorem orderedSignedScalarEquations_of_explicitHamiltonDerivatives
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitHamiltonDerivatives m kappa beta g p q)
    (time : Real) :
    HasDerivAt (orderedSignedPositionPath m k q)
        (orderedSignedMomentumPath m k p time) time ∧
      HasDerivAt (orderedSignedMomentumPath m k p)
        (-(orderedModeFrequency (harmonicHermitian m) k) ^ 2 *
            orderedSignedPositionPath m k q time +
          orderedSignedNonlinearForce m kappa beta g k (q time)) time := by
  have hweighted := massWeightedEquations_of_explicitHamiltonDerivatives
    m kappa beta g hDynamics time
  constructor
  · exact hasDerivAt_orderedSignedCoordinate m k hweighted.1
  · have hprojected := hasDerivAt_orderedSignedCoordinate m k hweighted.2
    unfold orderedSignedMomentumPath orderedSignedPositionPath
    have hlinear (X F : WeightedConfiguration N) :
        orderedSignedCoordinate m k (-harmonicOperator m X + F) =
          -orderedSignedCoordinate m k (harmonicOperator m X) +
            orderedSignedCoordinate m k F := by
      calc
        orderedSignedCoordinate m k (-harmonicOperator m X + F) =
            orderedSignedCoordinateCLM m k (-harmonicOperator m X + F) :=
          (orderedSignedCoordinateCLM_apply m k _).symm
        _ = -orderedSignedCoordinateCLM m k (harmonicOperator m X) +
              orderedSignedCoordinateCLM m k F := by
          rw [(orderedSignedCoordinateCLM m k).map_add]
          congr 1
          simpa only [LinearMap.neg_apply] using
            (orderedSignedCoordinateCLM m k).map_neg (harmonicOperator m X)
        _ = -orderedSignedCoordinate m k (harmonicOperator m X) +
              orderedSignedCoordinate m k F := by simp
    convert hprojected using 1
    rw [orderedModeFrequency_sq_eq_orderedEigenvalue]
    unfold orderedSignedNonlinearForce
    rw [hlinear, orderedSignedCoordinate_harmonicOperator m hsimple k]
    ring

omit [Fintype I] [DecidableEq I] in
/-- Interaction-picture amplitude path in the measurable signed frame. -/
def orderedSignedInteractionPath
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N)
    (p q : Real → HilbertConfiguration N) : Real → Complex :=
  fun s => phaseRenormalize
    (orderedModeFrequency (harmonicHermitian m) k * s)
    (complexModeAmplitude
      (orderedModeFrequency (harmonicHermitian m) k)
      (orderedSignedPositionPath m k q s)
      (orderedSignedMomentumPath m k p s))


omit [Fintype I] [DecidableEq I] in
/-- Exact derivative of the measurable-frame interaction amplitude along
any genuine coercive Hamilton trajectory. -/
theorem hasDerivAt_orderedSignedInteractionPath
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitHamiltonDerivatives m kappa beta g p q)
    (homega : 0 < orderedModeFrequency (harmonicHermitian m) k)
    (time : Real) :
    HasDerivAt (orderedSignedInteractionPath m k p q)
      (orderedSignedRotatedSource m kappa beta g k q time) time := by
  have hscalar := orderedSignedScalarEquations_of_explicitHamiltonDerivatives
    m kappa beta g hsimple k hDynamics time
  unfold orderedSignedInteractionPath orderedSignedRotatedSource
  apply hasDerivAt_interactionPicture
  exact hasDerivAt_complexModeAmplitude_forced
    (omega := orderedModeFrequency (harmonicHermitian m) k)
    (Q := orderedSignedPositionPath m k q) (P := orderedSignedMomentumPath m k p)
    (R := fun s => orderedSignedNonlinearForce m kappa beta g k (q s))
    homega hscalar.1 hscalar.2

end

end ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
