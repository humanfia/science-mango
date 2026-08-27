import ArchonPhysics.CyclicWindowPrefixComparison
import ArchonPhysics.PeriodicPolynomialWindowGeometricInterior

/-!
# Centered translated windows as cyclic starting windows

The centered-window reduction of a periodic kernel indexes a local window by
the unique cyclic shift sending its center to the chosen target site.  As the
target ranges over the cycle, those shifts form a permutation.  On the
canonical restriction of an infinite mass sequence, the translated window is
therefore exactly the ordinary cyclic window indexed by the shift value.
-/

namespace ArchonPhysics.CenteredTranslatedWindowAverage

open ArchonPhysics
open ArchonPhysics.CyclicWindowPrefixComparison
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Natural-coordinate formula for the cyclic translation on `Fin N`. -/
theorem finCycleTranslation_val {N : Nat} [NeZero N]
    (shift i : Fin N) :
    (finCycleTranslation shift i).val = (shift.val + i.val) % N := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

/-- Sending a fixed center to the target is a permutation of cyclic shifts. -/
def finCenteringShiftEquiv {N : Nat} [NeZero N]
    (center : Fin N) : Equiv.Perm (Fin N) where
  toFun target := finCenteringShift center target
  invFun shift := finCycleTranslation shift center
  left_inv target := finCycleTranslation_centeringShift_apply center target
  right_inv shift := by
    apply (siteEquivFin N).symm.injective
    simp [finCenteringShift, finCycleTranslation, siteTranslation,
      sub_eq_add_neg, add_assoc]

/-- A translated finite restriction of the infinite sequence is exactly the
cyclic window beginning at the natural value of the shift. -/
theorem translatedMassWindow_restrict_eq_cyclicMassWindow
    (ensemble : IIDMassPhaseEnsemble Omega)
    {n m : Nat} [NeZero (n + m)] (omega : Omega)
    (shift : Fin (n + m)) :
    translatedMassWindow
        (fun i : Fin (n + m) => ensemble.mass i.val omega) shift =
      cyclicMassWindow ensemble (n + m) n shift.val omega := by
  funext j
  unfold translatedMassWindow cyclicMassWindow
  change ensemble.mass (finCycleTranslation shift (Fin.castAdd m j)).val omega = _
  rw [finCycleTranslation_val]
  rfl

/-- Averaging centered translated windows over all target sites is exactly
the cyclic starting-window average. -/
theorem centeredTranslatedWindowAverage_eq_cyclicComplexWindowAverage
    (ensemble : IIDMassPhaseEnsemble Omega)
    {n m : Nat} [NeZero (n + m)] (omega : Omega)
    (center : Fin (n + m)) (f : (Fin n -> Real) -> Complex) :
    (∑ target : Fin (n + m),
        f (translatedMassWindow
          (fun i : Fin (n + m) => ensemble.mass i.val omega)
          (finCenteringShift center target))) / ((n + m : Nat) : Real) =
      cyclicComplexWindowAverage ensemble (n + m) n f omega := by
  unfold cyclicComplexWindowAverage
  congr 1
  calc
    (∑ target : Fin (n + m),
        f (translatedMassWindow
          (fun i : Fin (n + m) => ensemble.mass i.val omega)
          (finCenteringShift center target))) =
        ∑ shift : Fin (n + m),
          f (translatedMassWindow
            (fun i : Fin (n + m) => ensemble.mass i.val omega) shift) := by
      exact Equiv.sum_comp (finCenteringShiftEquiv center)
        (fun shift : Fin (n + m) =>
          f (translatedMassWindow
            (fun i : Fin (n + m) => ensemble.mass i.val omega) shift))
    _ = ∑ start ∈ Finset.range (n + m),
          f (cyclicMassWindow ensemble (n + m) n start omega) := by
      calc
        _ = ∑ shift : Fin (n + m),
            f (cyclicMassWindow ensemble (n + m) n shift.val omega) := by
          apply Finset.sum_congr rfl
          intro shift _hshift
          rw [translatedMassWindow_restrict_eq_cyclicMassWindow]
        _ = _ := Fin.sum_univ_eq_sum_range
          (fun start =>
            f (cyclicMassWindow ensemble (n + m) n start omega)) (n + m)

end

end ArchonPhysics.CenteredTranslatedWindowAverage
