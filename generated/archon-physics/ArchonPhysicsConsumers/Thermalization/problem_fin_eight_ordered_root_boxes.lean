import ArchonPhysics.FinEightOrderedRootBoxes

/-!
# Consumer: certified rank boxes for the eight-site spectral witness

This consumer records the three ranks needed by the candidate all-distinct
decay channel.  Concrete interval arithmetic and concrete root certificates
remain inputs; the ordering step itself is discharged by the generic core.
-/

open Set

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.FinEightOrderedRootBoxes

noncomputable section

theorem ranks_three_five_six_mem_certified_boxes
    (A : HermitianMatrix (Fin 8))
    (lower upper root : Fin 7 → Real)
    (hordered : ∀ {i j : Fin 7}, i < j → upper j < lower i)
    (hlowerPositive : ∀ k, 0 < lower k)
    (hbox : ∀ k, root k ∈ Ioo (lower k) (upper k))
    (hisRoot : ∀ k, Polynomial.eval (root k) (Matrix.charpoly A.1) = 0)
    (hzero : Polynomial.eval 0 (Matrix.charpoly A.1) = 0) :
    orderedEigenvalue A (Fin.castAdd 1 (3 : Fin 7)) ∈
        Ioo (lower 3) (upper 3) ∧
      orderedEigenvalue A (Fin.castAdd 1 (5 : Fin 7)) ∈
        Ioo (lower 5) (upper 5) ∧
      orderedEigenvalue A (Fin.castAdd 1 (6 : Fin 7)) ∈
        Ioo (lower 6) (upper 6) := by
  exact ⟨
    orderedEigenvalue_castAdd_mem_box A lower upper root hordered
      hlowerPositive hbox hisRoot hzero 3,
    orderedEigenvalue_castAdd_mem_box A lower upper root hordered
      hlowerPositive hbox hisRoot hzero 5,
    orderedEigenvalue_castAdd_mem_box A lower upper root hordered
      hlowerPositive hbox hisRoot hzero 6⟩

end

end ArchonPhysicsConsumers.Thermalization
