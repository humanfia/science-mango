import Mathlib.MeasureTheory.Constructions.Pi
import ArchonPhysics.PolynomialZeroSetNull
import ArchonPhysics.RandomEnsemble

/-!
# Finite iid mass samples avoid algebraic exceptional sets

The one-site mass law is normalized Lebesgue measure on a compact interval,
hence is absolutely continuous with respect to Lebesgue measure.  This module
propagates that fact to every finite iid product and combines it with
`volume_zeroSet_mvPolynomial_eval`: every nonzero real polynomial in finitely
many raw mass coordinates is nonzero almost surely.
-/

namespace ArchonPhysics

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace RandomEnsemble

/-- The joint law of `N` iid raw mass coordinates, indexed by `Fin N`. -/
def finiteMassLaw (N : Nat) : Measure (Fin N → Real) :=
  Measure.pi fun _ : Fin N => massCoordinateLaw

noncomputable instance finiteMassLaw.instIsProbabilityMeasure (N : Nat) :
    IsProbabilityMeasure (finiteMassLaw N) := by
  unfold finiteMassLaw
  infer_instance

/-- The bounded uniform one-coordinate mass law is absolutely continuous
with respect to Lebesgue measure. -/
theorem massCoordinateLaw_absolutelyContinuous_volume :
    massCoordinateLaw ≪ volume := by
  exact ProbabilityTheory.cond_absolutelyContinuous

/-- Every finite iid mass law is absolutely continuous with respect to
Lebesgue volume on its finite-dimensional coordinate space. -/
theorem finiteMassLaw_absolutelyContinuous_volume :
    ∀ N : Nat, finiteMassLaw N ≪ (volume : Measure (Fin N → Real))
  | 0 => by
      rw [finiteMassLaw, Measure.pi_of_empty, Measure.volume_pi_eq_dirac]
  | n + 1 => by
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Real) 0
      have hMass : MeasurePreserving e (finiteMassLaw (n + 1))
          (massCoordinateLaw.prod (finiteMassLaw n)) := by
        dsimp [e]
        simpa [finiteMassLaw] using
          measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => massCoordinateLaw) 0
      have hVolume : MeasurePreserving e
          (volume : Measure (Fin (n + 1) → Real))
          (volume : Measure (Real × (Fin n → Real))) := by
        exact volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => Real) 0
      have hProduct :
          massCoordinateLaw.prod (finiteMassLaw n) ≪
            (volume : Measure (Real × (Fin n → Real))) := by
        rw [Measure.volume_eq_prod]
        exact massCoordinateLaw_absolutelyContinuous_volume.prod
          (finiteMassLaw_absolutelyContinuous_volume n)
      have hMapped := e.symm.measurableEmbedding.absolutelyContinuous_map hProduct
      rw [(MeasurePreserving.symm e hMass).map_eq,
        (MeasurePreserving.symm e hVolume).map_eq] at hMapped
      exact hMapped

/-- A finite iid raw mass vector assigns probability zero to the zero set of
any nonzero real multivariate polynomial. -/
theorem finiteMassLaw_zeroSet_mvPolynomial_eval {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    finiteMassLaw N {x | MvPolynomial.eval x P = 0} = 0 := by
  exact finiteMassLaw_absolutelyContinuous_volume N
    (volume_zeroSet_mvPolynomial_eval P hP)

end RandomEnsemble

namespace IIDMassPhaseEnsemble

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The first `N` mass coordinates, indexed by `Fin N`.  For nonempty chains
this is the canonical `Fin N` reindexing of `restrictMass`. -/
def restrictMassFin (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat}
    (omega : Omega) : Fin N → Real :=
  fun i => ensemble.mass i.val omega

theorem measurable_restrictMassFin (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} : Measurable (ensemble.restrictMassFin (N := N)) := by
  exact measurable_pi_lambda _ fun i => ensemble.mass_measurable i.val

/-- The `Fin N` restriction has exactly the finite iid product mass law. -/
theorem restrictMassFin_hasLaw (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} :
    HasLaw (ensemble.restrictMassFin (N := N))
      (RandomEnsemble.finiteMassLaw N) ensemble.probability := by
  have hIndep : iIndepFun
      (fun i : Fin N => ensemble.mass i.val) ensemble.probability :=
    ensemble.mass_iIndep.precomp
      (g := fun i : Fin N => i.val) Fin.val_injective
  have hLaw := hIndep.hasLaw_pi fun i : Fin N => ensemble.mass_hasLaw i.val
  change HasLaw (fun (omega : Omega) (i : Fin N) => ensemble.mass i.val omega)
    (RandomEnsemble.finiteMassLaw N) ensemble.probability
  simpa [RandomEnsemble.finiteMassLaw] using hLaw

/-- The `Fin N` restriction agrees with the existing periodic-site
restriction after the natural `Fin N → ZMod N` reindexing. -/
theorem restrictMassFin_eq_restrictMass
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (omega : Omega) (i : Fin N) :
    ensemble.restrictMassFin omega i =
      ensemble.restrictMass omega (i.val : Lattice.Site N) := by
  rw [restrictMassFin, restrictMass, ZMod.val_cast_of_lt i.isLt]

/-- In every verified iid mass-phase ensemble, a nonzero polynomial of the
first `N` raw masses vanishes with probability zero. -/
theorem probability_restrictMassFin_mvPolynomial_eval_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    ensemble.probability
        {omega | MvPolynomial.eval (ensemble.restrictMassFin omega) P = 0} = 0 := by
  have hLaw := ensemble.restrictMassFin_hasLaw (N := N)
  have hMeasurable : MeasurableSet
      {x : Fin N → Real | MvPolynomial.eval x P = 0} :=
    (isClosed_singleton.preimage P.continuous_eval).measurableSet
  exact (hLaw.measure_eq hMeasurable).trans
    (RandomEnsemble.finiteMassLaw_zeroSet_mvPolynomial_eval P hP)

/-- Equivalent almost-sure form of polynomial avoidance. -/
theorem restrictMassFin_mvPolynomial_eval_ne_zero_ae
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    ∀ᵐ omega ∂ensemble.probability,
      MvPolynomial.eval (ensemble.restrictMassFin omega) P ≠ 0 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (ensemble.probability_restrictMassFin_mvPolynomial_eval_eq_zero P hP)] with omega homega
  simpa only [Set.mem_ofPred_eq] using homega

end IIDMassPhaseEnsemble

end

end ArchonPhysics
