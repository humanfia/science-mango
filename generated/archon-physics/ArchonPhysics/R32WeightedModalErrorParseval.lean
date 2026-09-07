import ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5
import ArchonPhysics.R32ModalEnergyL1Stability

/-!
# Exact Parseval bridge for the R32 harmonic error energy

This file identifies the frequency-weighted ordered-modal `L2` distance with
the harmonic error seminorm in mass-weighted site coordinates.  The result is
finite-dimensional and coefficient-exact; it introduces no probabilistic or
long-time premise.
-/

namespace ArchonPhysics.R32WeightedModalErrorParseval

open ArchonPhysics
open ArchonPhysics.FiniteModalEnergyL1Stability
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5
open ArchonPhysics.R32ModalEnergyL1Stability
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.SpectralBandEnergyObservable
open scoped Matrix RealInnerProductSpace

noncomputable section

variable {N : Nat} [NeZero N]

theorem phaseSpaceL2Norm_eq_piLpNorm
    {Mode : Type} [Fintype Mode] (W : Mode → Complex) :
    phaseSpaceL2Norm W = ‖WithLp.toLp 2 W‖ := by
  unfold phaseSpaceL2Norm amplitudeL2Norm
  rw [PiLp.norm_eq_of_L2]

/-- Triangle inequality in the unbundled modal notation used by the
late-window stability layer. -/
theorem phaseSpaceL2Norm_le_distance_add
    {Mode : Type} [Fintype Mode] (W W0 : Mode → Complex) :
    phaseSpaceL2Norm W ≤
      phaseSpaceL2Distance W W0 + phaseSpaceL2Norm W0 := by
  rw [phaseSpaceL2Norm_eq_piLpNorm, phaseSpaceL2Norm_eq_piLpNorm]
  have hdistance : phaseSpaceL2Distance W W0 =
      ‖WithLp.toLp 2 W - WithLp.toLp 2 W0‖ := by
    unfold phaseSpaceL2Distance amplitudeL2Distance
    rw [PiLp.norm_eq_of_L2]
    congr 1
  rw [hdistance]
  have hdecomp : WithLp.toLp 2 W =
      (WithLp.toLp 2 W - WithLp.toLp 2 W0) + WithLp.toLp 2 W0 := by
    abel
  calc
    ‖WithLp.toLp 2 W‖ =
        ‖(WithLp.toLp 2 W - WithLp.toLp 2 W0) +
          WithLp.toLp 2 W0‖ := congrArg norm hdecomp
    _ ≤ ‖WithLp.toLp 2 W - WithLp.toLp 2 W0‖ +
        ‖WithLp.toLp 2 W0‖ := norm_add_le _ _

/-- Frequency-weighted ordered modal vector written directly in the
mass-weighted site variables `X = sqrt(M)q`, `Y = M^(-1/2)p`. -/
def weightedOrderedHarmonicPhaseVector
    (m : Lattice.PositiveMassConfig N)
    (x y : WeightedConfiguration N) : OrderedModeIndex N → Complex :=
  orderedHarmonicPhaseVector (harmonicHermitian m)
    (WithLp.ofLp x) (WithLp.ofLp y)

theorem weightedOrderedHarmonicPhaseVector_sub
    (m : Lattice.PositiveMassConfig N)
    (x y x0 y0 : WeightedConfiguration N) :
    weightedOrderedHarmonicPhaseVector m x y -
        weightedOrderedHarmonicPhaseVector m x0 y0 =
      weightedOrderedHarmonicPhaseVector m (x - x0) (y - y0) := by
  funext k
  apply Complex.ext
  · simp [weightedOrderedHarmonicPhaseVector,
      orderedHarmonicPhaseVector, orderedSignedCoordinate, dotProduct,
      Finset.sum_sub_distrib, mul_sub]
  · simp [weightedOrderedHarmonicPhaseVector,
      orderedHarmonicPhaseVector, orderedSignedCoordinate, dotProduct,
      Finset.sum_sub_distrib, mul_sub]

/-- Parseval for one mass-weighted phase point: the squared modal `L2` norm
is the kinetic norm square plus the harmonic quadratic form. -/
theorem phaseSpaceL2Norm_weighted_sq
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (x y : WeightedConfiguration N) :
    phaseSpaceL2Norm (weightedOrderedHarmonicPhaseVector m x y) ^ 2 =
      ‖y‖ ^ 2 +
        @inner Real (WeightedConfiguration N) _ x (harmonicOperator m x) := by
  have hmode : ∀ k : OrderedModeIndex N,
      ‖weightedOrderedHarmonicPhaseVector m x y k‖ ^ 2 =
        2 * orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) := by
    intro k
    simpa only [weightedOrderedHarmonicPhaseVector] using
      norm_sq_orderedHarmonicPhaseVector
        (harmonicHermitian m) hsimple
        (harmonicHermitian_orderedEigenvalue_nonneg m)
        (WithLp.ofLp x) (WithLp.ofLp y) k
  have hsum := sum_orderedHarmonicModeEnergy
    (harmonicHermitian m) hsimple (WithLp.ofLp x) (WithLp.ofLp y)
  have hsumNonneg :
      0 ≤ ∑ k : OrderedModeIndex N,
        ‖weightedOrderedHarmonicPhaseVector m x y k‖ ^ 2 :=
    Finset.sum_nonneg fun k _hk => sq_nonneg _
  have hkinetic :
      coordinateEnergy (WithLp.ofLp y) = ‖y‖ ^ 2 := by
    unfold coordinateEnergy
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  have hpotential :
      dotProduct (WithLp.ofLp x)
          (Matrix.mulVec (matrixVal (harmonicHermitian m))
            (WithLp.ofLp x)) =
        @inner Real (WeightedConfiguration N) _ x
          (harmonicOperator m x) := by
    simp only [harmonicHermitian, harmonicOperator_apply,
      PiLp.inner_apply, dotProduct]
    apply Finset.sum_congr rfl
    intro i _hi
    change (WithLp.ofLp x) i *
        (massWeightedHarmonicMatrix m *ᵥ WithLp.ofLp x) i =
      (massWeightedHarmonicMatrix m *ᵥ WithLp.ofLp x) i *
        (WithLp.ofLp x) i
    exact mul_comm _ _
  unfold phaseSpaceL2Norm amplitudeL2Norm
  rw [Real.sq_sqrt hsumNonneg]
  calc
      (∑ k : OrderedModeIndex N,
          ‖weightedOrderedHarmonicPhaseVector m x y k‖ ^ 2) =
          ∑ k : OrderedModeIndex N,
            2 * orderedHarmonicModeEnergy (harmonicHermitian m) k
              (WithLp.ofLp x) (WithLp.ofLp y) := by
            exact Finset.sum_congr rfl fun k _hk => hmode k
      _ = 2 * (∑ k : OrderedModeIndex N,
            orderedHarmonicModeEnergy (harmonicHermitian m) k
              (WithLp.ofLp x) (WithLp.ofLp y)) := by
            rw [Finset.mul_sum]
      _ = coordinateEnergy (WithLp.ofLp y) +
            dotProduct (WithLp.ofLp x)
              (Matrix.mulVec (matrixVal (harmonicHermitian m))
                (WithLp.ofLp x)) := by
            rw [hsum]
            ring
      _ = ‖y‖ ^ 2 +
            @inner Real (WeightedConfiguration N) _ x
              (harmonicOperator m x) := by
            rw [hkinetic, hpotential]

/-- Equivalent modal-energy form of Parseval. -/
theorem phaseSpaceL2Norm_weighted_sq_eq_two_sum
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (x y : WeightedConfiguration N) :
    phaseSpaceL2Norm (weightedOrderedHarmonicPhaseVector m x y) ^ 2 =
      2 * ∑ k : OrderedModeIndex N,
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) := by
  have hsumNonneg :
      0 ≤ ∑ k : OrderedModeIndex N,
        ‖weightedOrderedHarmonicPhaseVector m x y k‖ ^ 2 :=
    Finset.sum_nonneg fun _k _hk => sq_nonneg _
  unfold phaseSpaceL2Norm amplitudeL2Norm
  rw [Real.sq_sqrt hsumNonneg]
  calc
    (∑ k : OrderedModeIndex N,
        ‖weightedOrderedHarmonicPhaseVector m x y k‖ ^ 2) =
        ∑ k : OrderedModeIndex N,
          2 * orderedHarmonicModeEnergy (harmonicHermitian m) k
            (WithLp.ofLp x) (WithLp.ofLp y) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact norm_sq_orderedHarmonicPhaseVector
        (harmonicHermitian m) hsimple
        (harmonicHermitian_orderedEigenvalue_nonneg m)
        (WithLp.ofLp x) (WithLp.ofLp y) k
    _ = 2 * ∑ k : OrderedModeIndex N,
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) := by
      rw [Finset.mul_sum]

/-- Exact equality between the modal phase-space distance and the harmonic
energy seminorm of the site-coordinate difference. -/
theorem phaseSpaceL2Distance_weighted_eq_harmonicEnergySeminorm
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (x y x0 y0 : WeightedConfiguration N) :
    phaseSpaceL2Distance
        (weightedOrderedHarmonicPhaseVector m x y)
        (weightedOrderedHarmonicPhaseVector m x0 y0) =
      harmonicEnergySeminorm
        (LinearMap.toContinuousLinearMap (harmonicOperator m))
        (x - x0) (y - y0) := by
  change Real.sqrt
      (∑ k : OrderedModeIndex N,
        ‖(weightedOrderedHarmonicPhaseVector m x y -
          weightedOrderedHarmonicPhaseVector m x0 y0) k‖ ^ 2) = _
  rw [weightedOrderedHarmonicPhaseVector_sub]
  change phaseSpaceL2Norm
      (weightedOrderedHarmonicPhaseVector m (x - x0) (y - y0)) = _
  unfold harmonicEnergySeminorm harmonicEnergySq
  change phaseSpaceL2Norm
      (weightedOrderedHarmonicPhaseVector m (x - x0) (y - y0)) =
    Real.sqrt (‖y - y0‖ ^ 2 +
      @inner Real (WeightedConfiguration N) _ (x - x0)
        (harmonicOperator m (x - x0)))
  rw [← phaseSpaceL2Norm_weighted_sq m hsimple (x - x0) (y - y0)]
  simpa only [phaseSpaceL2Norm] using
    (Real.sqrt_sq
      (amplitudeL2Norm_nonneg
        (weightedOrderedHarmonicPhaseVector m (x - x0) (y - y0)))).symm

/-- Dimension-free raw modal-energy `L1` bound in terms of the harmonic
error and a norm ceiling for the free comparison state. -/
theorem orderedHarmonicModeEnergy_l1_le_of_weighted_error
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (x y x0 y0 : WeightedConfiguration N)
    (error freeCeiling : Real)
    (herror0 : 0 ≤ error) (hfreeCeiling0 : 0 ≤ freeCeiling)
    (hdistance : phaseSpaceL2Distance
      (weightedOrderedHarmonicPhaseVector m x y)
      (weightedOrderedHarmonicPhaseVector m x0 y0) ≤ error)
    (hfreeNorm : phaseSpaceL2Norm
      (weightedOrderedHarmonicPhaseVector m x0 y0) ≤ freeCeiling) :
    (∑ k : OrderedModeIndex N,
      |orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) -
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x0) (WithLp.ofLp y0)|) ≤
      (1 / 2 : Real) * error * (error + 2 * freeCeiling) := by
  let W := weightedOrderedHarmonicPhaseVector m x y
  let W0 := weightedOrderedHarmonicPhaseVector m x0 y0
  have hnorm : phaseSpaceL2Norm W ≤ error + freeCeiling := by
    exact (phaseSpaceL2Norm_le_distance_add W W0).trans
      (add_le_add hdistance hfreeNorm)
  have hbase := orderedHarmonicModeEnergy_l1_le
    (harmonicHermitian m) hsimple
    (harmonicHermitian_orderedEigenvalue_nonneg m)
    (WithLp.ofLp x) (WithLp.ofLp y)
    (WithLp.ofLp x0) (WithLp.ofLp y0)
  change (∑ k : OrderedModeIndex N,
      |orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) -
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x0) (WithLp.ofLp y0)|) ≤
    (1 / 2 : Real) * phaseSpaceL2Distance W W0 *
      (phaseSpaceL2Norm W + phaseSpaceL2Norm W0) at hbase
  calc
    (∑ k : OrderedModeIndex N,
      |orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x) (WithLp.ofLp y) -
        orderedHarmonicModeEnergy (harmonicHermitian m) k
          (WithLp.ofLp x0) (WithLp.ofLp y0)|) ≤
        (1 / 2 : Real) * phaseSpaceL2Distance W W0 *
          (phaseSpaceL2Norm W + phaseSpaceL2Norm W0) := hbase
    _ ≤ (1 / 2 : Real) * error *
          ((error + freeCeiling) + freeCeiling) := by
      gcongr
      exact add_nonneg (amplitudeL2Norm_nonneg W)
        (amplitudeL2Norm_nonneg W0)
    _ = (1 / 2 : Real) * error * (error + 2 * freeCeiling) := by
      ring

#print axioms phaseSpaceL2Norm_weighted_sq
#print axioms phaseSpaceL2Norm_weighted_sq_eq_two_sum
#print axioms phaseSpaceL2Distance_weighted_eq_harmonicEnergySeminorm
#print axioms phaseSpaceL2Norm_le_distance_add
#print axioms orderedHarmonicModeEnergy_l1_le_of_weighted_error

end

end ArchonPhysics.R32WeightedModalErrorParseval
