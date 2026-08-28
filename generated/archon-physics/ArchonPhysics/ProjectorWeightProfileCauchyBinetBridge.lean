import ArchonPhysics.ActualThreeMassProjectorWeightJacobian
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Projector-weight profile Gram-to-minor bridge

For a real `3 × N` profile matrix, a nonzero row Gram determinant forces the
rows to have full rank.  A basis extracted from the span of all columns then
selects three actual columns with nonzero determinant.  The selected-column
map is automatically injective, since repeated columns would make that
determinant vanish.

This is the existence direction of Cauchy--Binet needed by the random-mass
projector problem.  It avoids introducing a nondegeneracy premise: the Gram
determinant remains an explicit antecedent.  The final results specialize the
bridge to the genuine ordered spectral-projector weights along all physical
cycle mass-perturbation directions.
-/

open scoped Matrix

namespace ArchonPhysics.ProjectorWeightProfileCauchyBinetBridge

open ArchonPhysics
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open Function Set Submodule

noncomputable section

/-- Full row rank of a real `3 × N` matrix lets one select three actual
columns forming a nonsingular square minor. -/
theorem exists_injective_threeColumnMinor_ne_zero_of_linearIndependent_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin 3) ι Real)
    (hrows : LinearIndependent Real Q.row) :
    ∃ sites : Fin 3 → ι, Function.Injective sites ∧
      (Q.submatrix id sites).det ≠ 0 := by
  let columnSpan : Submodule Real (Fin 3 → Real) :=
    Submodule.span Real (Set.range Q.col)
  have hrank : Q.rank = 3 := by
    simpa using hrows.rank_matrix
  have hfinrank : Module.finrank Real columnSpan =
      Module.finrank Real (Fin 3 → Real) := by
    rw [show Module.finrank Real columnSpan = Q.rank by
      exact (Q.rank_eq_finrank_span_cols).symm]
    rw [hrank]
    simp
  have hspanEq : columnSpan = ⊤ :=
    Submodule.eq_top_of_finrank_eq hfinrank
  have hspan : ⊤ ≤ Submodule.span Real (Set.range Q.col) := by
    simpa [columnSpan] using hspanEq.ge
  let b := Module.Basis.ofSpan hspan
  let J := (linearIndepOn_empty Real id).extend
    (empty_subset (Set.range Q.col))
  let _ : Fintype J := Fintype.ofFinite J
  have hcardJ : Fintype.card J = 3 := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin 3 ≃ J := Fintype.equivOfCardEq (by simpa using hcardJ.symm)
  have hbmem (s : Fin 3) : b (e s) ∈ Set.range Q.col := by
    apply Module.Basis.ofSpan_subset hspan
    exact Set.mem_range_self (e s)
  choose sites hsites using hbmem
  let M : Matrix (Fin 3) (Fin 3) Real := Q.submatrix id sites
  have hcols : LinearIndependent Real M.col := by
    have hb : LinearIndependent Real (fun s : Fin 3 => b (e s)) :=
      b.linearIndependent.comp e e.injective
    have hcolEq : M.col = fun s : Fin 3 => b (e s) := by
      funext s
      funext r
      change Q r (sites s) = b (e s) r
      exact congrFun (hsites s) r
    rw [hcolEq]
    exact hb
  have hnonsingular : M.Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_col hcols
  have hdet : M.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp hnonsingular
  refine ⟨sites, ?_, hdet⟩
  intro s t hsite
  by_contra hst
  apply hdet
  apply Matrix.det_zero_of_column_eq hst
  intro r
  simp [M, hsite]

/-- Gram nondegeneracy is enough to trigger the column-basis extraction. -/
theorem exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin 3) ι Real)
    (hgram : (Q * Q.transpose).det ≠ 0) :
    ∃ sites : Fin 3 → ι, Function.Injective sites ∧
      (Q.submatrix id sites).det ≠ 0 := by
  apply exists_injective_threeColumnMinor_ne_zero_of_linearIndependent_rows Q
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin 3) =
    Module.finrank Real (Submodule.span Real (Set.range Q.row))
  rw [← Q.rank_eq_finrank_span_row]
  have hgramRank : (Q * Q.transpose).rank = 3 := by
    simpa using Matrix.rank_of_det_ne_zero hgram
  have hQRank : Q.rank = 3 := by
    rw [Matrix.rank_self_mul_transpose] at hgramRank
    exact hgramRank
  simpa using hQRank.symm

/-- Contrapositive form: if every injectively selected three-column minor
vanishes, then the row Gram determinant vanishes. -/
theorem gram_det_eq_zero_of_all_injective_threeColumnMinor_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin 3) ι Real)
    (hminor : ∀ sites : Fin 3 → ι, Function.Injective sites →
      (Q.submatrix id sites).det = 0) :
    (Q * Q.transpose).det = 0 := by
  by_contra hgram
  obtain ⟨sites, hinjective, hdet⟩ :=
    exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero Q hgram
  exact hdet (hminor sites hinjective)

/-- The actual `3 × N` projector-weight profile along every physical cycle
mass-perturbation direction. -/
def orderedCycleProjectorWeightProfile
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Matrix (Fin 3) (Lattice.Site N) Real :=
  fun r site =>
    cycleMassPerturbationVector site ⬝ᵥ
      (orderedModeProjector A (modes r) *ᵥ
        cycleMassPerturbationVector site)

/-- Selecting three columns of the full physical profile is exactly the
existing ordered projector-weight matrix for those three cycle directions. -/
theorem orderedCycleProjectorWeightProfile_submatrix
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (sites : Fin 3 → Lattice.Site N) :
    (orderedCycleProjectorWeightProfile A modes).submatrix id sites =
      orderedProjectorWeightMatrix A modes
        (fun s => cycleMassPerturbationVector (sites s)) := by
  rfl

/-- Actual cycle-profile specialization: a nonzero Gram determinant supplies
three distinct physical mass sites with a nonzero genuine projector minor. -/
theorem exists_injective_cycleSites_projectorMinor_ne_zero_of_profileGram_det_ne_zero
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hgram :
      (orderedCycleProjectorWeightProfile A modes *
        (orderedCycleProjectorWeightProfile A modes).transpose).det ≠ 0) :
    ∃ sites : Fin 3 → Lattice.Site N, Function.Injective sites ∧
      (orderedProjectorWeightMatrix A modes
        (fun s => cycleMassPerturbationVector (sites s))).det ≠ 0 := by
  obtain ⟨sites, hinjective, hminor⟩ :=
    exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero
      (orderedCycleProjectorWeightProfile A modes) hgram
  refine ⟨sites, hinjective, ?_⟩
  rw [← orderedCycleProjectorWeightProfile_submatrix]
  exact hminor

/-- Vanishing of every distinct-site actual projector minor forces the full
physical projector-profile Gram determinant to vanish. -/
theorem profileGram_det_eq_zero_of_all_injective_cycleSite_projectorMinor_eq_zero
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hminor : ∀ sites : Fin 3 → Lattice.Site N,
      Function.Injective sites →
      (orderedProjectorWeightMatrix A modes
        (fun s => cycleMassPerturbationVector (sites s))).det = 0) :
    (orderedCycleProjectorWeightProfile A modes *
      (orderedCycleProjectorWeightProfile A modes).transpose).det = 0 := by
  apply gram_det_eq_zero_of_all_injective_threeColumnMinor_eq_zero
  intro sites hinjective
  rw [orderedCycleProjectorWeightProfile_submatrix]
  exact hminor sites hinjective

end

end ArchonPhysics.ProjectorWeightProfileCauchyBinetBridge
