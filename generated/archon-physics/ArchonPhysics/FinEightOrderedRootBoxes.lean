import ArchonPhysics.MeasurableOrderedSpectrum

/-!
# Ordered spectral bounds from seven positive root boxes in dimension eight

This file is a generic bridge from certified characteristic-polynomial roots
to Mathlib's decreasing Hermitian spectrum.  Seven strictly ordered positive
root boxes and the exact root zero already exhaust a degree-eight
characteristic polynomial.  No concrete matrix arithmetic is used here.
-/

open Set

namespace ArchonPhysics.FinEightOrderedRootBoxes

open ArchonPhysics.MeasurableOrderedSpectrum

noncomputable section

/-- Extend seven proposed positive eigenvalues by the acoustic zero at the
last decreasing spectral rank. -/
def rootsWithZero (root : Fin 7 → Real) : Fin 8 → Real := fun k ↦
  if hk : k.val < 7 then root ⟨k.val, hk⟩ else 0

@[simp] theorem rootsWithZero_castAdd (root : Fin 7 → Real) (k : Fin 7) :
    rootsWithZero root (Fin.castAdd 1 k) = root k := by
  simp [rootsWithZero]

@[simp] theorem rootsWithZero_last (root : Fin 7 → Real) :
    rootsWithZero root (7 : Fin 8) = 0 := by
  simp [rootsWithZero]

theorem rootsWithZero_strictAnti
    {root : Fin 7 → Real}
    (hroot : StrictAnti root)
    (hpositive : ∀ k, 0 < root k) :
    StrictAnti (rootsWithZero root) := by
  intro i j hij
  unfold rootsWithZero
  by_cases hi : i.val < 7
  · by_cases hj : j.val < 7
    · simp only [dif_pos hi, dif_pos hj]
      exact hroot (Fin.mk_lt_mk.mpr hij)
    · simp only [dif_pos hi, dif_neg hj]
      exact hpositive ⟨i.val, hi⟩
  · by_cases hj : j.val < 7
    · omega
    · omega

/-- Strictly decreasing disjoint boxes force any chosen point in each box to
be strictly decreasing. -/
theorem strictAnti_of_mem_orderedBoxes
    {lower upper root : Fin 7 → Real}
    (hordered : ∀ {i j : Fin 7}, i < j → upper j < lower i)
    (hbox : ∀ k, root k ∈ Ioo (lower k) (upper k)) :
    StrictAnti root := by
  intro i j hij
  exact (hbox j).2.trans ((hordered hij).trans (hbox i).1)

/-- Seven distinct positive roots and the root zero exhaust the full
characteristic polynomial of a Hermitian `Fin 8` matrix.  Therefore the
decreasing ordered eigenvalues are precisely those seven roots followed by
zero. -/
theorem orderedEigenvalue_eq_rootsWithZero_of_isRoot
    (A : HermitianMatrix (Fin 8))
    (root : Fin 7 → Real)
    (hroot : StrictAnti root)
    (hpositive : ∀ k, 0 < root k)
    (hisRoot : ∀ k, Polynomial.eval (root k) (Matrix.charpoly A.1) = 0)
    (hzero : Polynomial.eval 0 (Matrix.charpoly A.1) = 0) :
    ∀ k : Fin 8, orderedEigenvalue A k = rootsWithZero root k := by
  let energy : Fin 8 → Real := rootsWithZero root
  have henergyStrict : StrictAnti energy :=
    rootsWithZero_strictAnti hroot hpositive
  have henergyInjective : Function.Injective energy := henergyStrict.injective
  let rootSet : Finset Real := Finset.univ.image energy
  have hrootSetCard : rootSet.card = 8 := by
    simpa [rootSet] using Finset.card_image_of_injective Finset.univ henergyInjective
  have hrootSetEval : ∀ x ∈ rootSet,
      Polynomial.eval x (Matrix.charpoly A.1) = 0 := by
    intro x hx
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
    by_cases hk7 : k.val < 7
    · simpa [energy, rootsWithZero, hk7] using hisRoot ⟨k.val, hk7⟩
    · have hk : k = (7 : Fin 8) := by
        apply Fin.ext
        omega
      subst k
      simpa [energy] using hzero
  have hrootsSet : (Matrix.charpoly A.1).roots = rootSet.val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hrootSetEval
    · have hdegree : (Matrix.charpoly A.1).natDegree = 8 := by
        simpa using Matrix.charpoly_natDegree_eq_dim A.1
      rw [hdegree, hrootSetCard]
    · exact (Matrix.charpoly_monic A.1).ne_zero
  have hrootSetVal : rootSet.val = Multiset.map energy Finset.univ.val := by
    rw [show rootSet.val =
        (Multiset.map energy Finset.univ.val).dedup by
      simp only [rootSet, Finset.image_val]]
    exact Multiset.dedup_eq_self.mpr (Finset.univ.nodup.map henergyInjective)
  have hroots : (Matrix.charpoly A.1).roots =
      Multiset.map energy Finset.univ.val := hrootsSet.trans hrootSetVal
  have hsort := A.2.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  have hsort' :
      (Multiset.map energy Finset.univ.val).sort (· ≥ ·) =
        List.ofFn (fun k ↦ orderedEigenvalue A k) := by
    simpa [orderedEigenvalue, Function.comp_def] using hsort
  have henergySort :
      (Multiset.map energy Finset.univ.val).sort (· ≥ ·) =
        List.ofFn energy := by
    simp only [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact henergyStrict.antitone.sortedGE_ofFn
  have hlist : List.ofFn (fun k ↦ orderedEigenvalue A k) =
      List.ofFn energy := hsort'.symm.trans henergySort
  exact fun k ↦ congrFun (List.ofFn_inj.mp hlist) k

/-- Root boxes directly bind every positive ordered rank to its matching
box.  The theorem only asks that a root has been certified in every box and
that zero is an exact root. -/
theorem orderedEigenvalue_castAdd_mem_box
    (A : HermitianMatrix (Fin 8))
    (lower upper root : Fin 7 → Real)
    (hordered : ∀ {i j : Fin 7}, i < j → upper j < lower i)
    (hlowerPositive : ∀ k, 0 < lower k)
    (hbox : ∀ k, root k ∈ Ioo (lower k) (upper k))
    (hisRoot : ∀ k, Polynomial.eval (root k) (Matrix.charpoly A.1) = 0)
    (hzero : Polynomial.eval 0 (Matrix.charpoly A.1) = 0)
    (k : Fin 7) :
    orderedEigenvalue A (Fin.castAdd 1 k) ∈ Ioo (lower k) (upper k) := by
  have hstrict : StrictAnti root := strictAnti_of_mem_orderedBoxes hordered hbox
  have hpositive : ∀ k, 0 < root k := fun k ↦
    (hlowerPositive k).trans (hbox k).1
  rw [orderedEigenvalue_eq_rootsWithZero_of_isRoot A root hstrict hpositive
    hisRoot hzero, rootsWithZero_castAdd]
  exact hbox k

/-- The acoustic rank is exactly zero under the same seven-root-box
certificate. -/
theorem orderedEigenvalue_last_eq_zero
    (A : HermitianMatrix (Fin 8))
    (lower upper root : Fin 7 → Real)
    (hordered : ∀ {i j : Fin 7}, i < j → upper j < lower i)
    (hlowerPositive : ∀ k, 0 < lower k)
    (hbox : ∀ k, root k ∈ Ioo (lower k) (upper k))
    (hisRoot : ∀ k, Polynomial.eval (root k) (Matrix.charpoly A.1) = 0)
    (hzero : Polynomial.eval 0 (Matrix.charpoly A.1) = 0) :
    orderedEigenvalue A (7 : Fin 8) = 0 := by
  have hstrict : StrictAnti root := strictAnti_of_mem_orderedBoxes hordered hbox
  have hpositive : ∀ k, 0 < root k := fun k ↦
    (hlowerPositive k).trans (hbox k).1
  rw [orderedEigenvalue_eq_rootsWithZero_of_isRoot A root hstrict hpositive
    hisRoot hzero, rootsWithZero_last]

end

end ArchonPhysics.FinEightOrderedRootBoxes
