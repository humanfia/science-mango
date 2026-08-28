import ArchonPhysics.EvenVolumeWeakPathTwoToOneResultant

/-!
# Consumer: even-volume positive weak-path two-to-one resultant witness

For every even volume `2k+2`, a broken cycle with one strictly positive,
volume-dependent weak path edge has no exact fourfold ratio in its reduced
spectrum.  This supplies an unconditional nonzero specialization of the
symbolic two-to-one resultant certificate.

The parameter is selected existentially by finite-dimensional spectral
continuity.  No quantitative mismatch gap or uniform-in-volume lower bound is
claimed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EvenVolumeWeakPathTwoToOneResultant
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OddVolumePathTwoToOneResultant

noncomputable section

/-- A strictly positive weak edge excludes every exact fourfold ratio in the
reduced edge spectrum at each even volume. -/
theorem problem_evenVolume_exists_positiveWeakPath_all_fourfold_ne (k : Nat) :
    ∃ t : Real, 0 < t ∧
      ∀ i j : Fin (Fintype.card (Fin (2 * k + 1))),
        orderedEigenvalue (evenWeakPathHermitianMatrix (2 * k) t) i ≠
          4 * orderedEigenvalue
            (evenWeakPathHermitianMatrix (2 * k) t) j :=
  exists_pos_evenWeakPath_all_fourfold_ne k

/-- At that positive weak-path specialization, the physical zero-mode-reduced
characteristic polynomial has nonzero fourfold scale-roots resultant. -/
theorem problem_evenVolume_exists_positiveWeakPath_reduced_resultant_ne_zero
    (k : Nat) :
    ∃ t : Real, 0 < t ∧
      let p := (weightedCycleLaplacian
        (weightsOfCoordinates
          (evenWeakPathCoordinates (2 * k) t))).charpoly.divX
      Polynomial.resultant p (p.scaleRoots 4)
        p.natDegree p.natDegree ≠ 0 :=
  exists_pos_weightedCycle_evenWeakPath_reduced_resultant_ne_zero k

/-- Consequently the symbolic inverse-mass fourfold scale-roots resultant is
a genuinely nonzero polynomial at every even volume. -/
theorem problem_evenVolume_symbolicTwoToOneResultantCertificate_ne_zero
    (k : Nat) :
    symbolicTwoToOneResultantCertificate (N := 2 * k + 2) ≠ 0 :=
  symbolicTwoToOneResultantCertificate_ne_zero_evenSize k

#print axioms problem_evenVolume_exists_positiveWeakPath_all_fourfold_ne
#print axioms
  problem_evenVolume_exists_positiveWeakPath_reduced_resultant_ne_zero
#print axioms
  problem_evenVolume_symbolicTwoToOneResultantCertificate_ne_zero

end

end ArchonPhysicsConsumers.Thermalization
