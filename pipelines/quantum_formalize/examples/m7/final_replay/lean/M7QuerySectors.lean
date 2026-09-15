import M7DefaultQueryAccepted
import M7RecipeSignatureAccepted
import M7PrefixSectorAccepted
namespace M7.QuerySectors
/-- Multiset powerset retains every allowed multiplicity of every factor. -/
noncomputable def allSectors (N : ℕ) : Finset M6.Cyclic.BinaryPolynomial := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors (M6.Cyclic.modulus N)).powerset.toFinset.image Multiset.prod
noncomputable def effective (N : ℕ) (q : M7.DefaultQuery.Query) : Finset M6.Cyclic.BinaryPolynomial :=
  match q.signatures with
  | none => allSectors N
  | some E => E
end M7.QuerySectors
