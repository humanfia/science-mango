import ArchonPhysics.OddVolumePathTwoToOneResultant

/-!
# Consumer: odd-volume broken-path two-to-one resultant witness

These endpoints expose an unconditional algebraic specialization for every
odd volume `2k+1`.  The specialization breaks one cycle edge, so it proves
that the symbolic inverse-mass resultant polynomial is nonzero; it is not
itself a strictly positive random-mass realization.  No even-volume or
uniform-in-volume lower bound is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.OddVolumePathTwoToOneResultant
open ArchonPhysics.PathLaplacianSpecialization

noncomputable section

/-- The explicit broken unit path has nonzero reduced fourfold root-ratio
resultant at every odd volume. -/
theorem problem_oddVolume_brokenPath_reduced_resultant_ne_zero (k : Nat) :
    let p := (weightedCycleLaplacian
      (pathWeight (N := 2 * k + 1))).charpoly.divX
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 :=
  weightedCycleLaplacian_unitPath_reduced_resultant_ne_zero k

/-- Consequently the symbolic inverse-mass fourfold scale-roots resultant
is a genuinely nonzero polynomial for every odd volume. -/
theorem problem_oddVolume_symbolicTwoToOneResultantCertificate_ne_zero
    (k : Nat) :
    symbolicTwoToOneResultantCertificate (N := 2 * k + 1) ≠ 0 :=
  symbolicTwoToOneResultantCertificate_ne_zero_oddSize k

#print axioms problem_oddVolume_brokenPath_reduced_resultant_ne_zero
#print axioms
  problem_oddVolume_symbolicTwoToOneResultantCertificate_ne_zero

end

end ArchonPhysicsConsumers.Thermalization
