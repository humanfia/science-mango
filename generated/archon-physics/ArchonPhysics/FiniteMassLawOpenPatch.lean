import ArchonPhysics.FiniteMassPolynomialAvoidance

/-!
# Positive finite iid mass on interior open patches

The canonical one-site mass law is normalized Lebesgue measure on
`[4/5, 6/5]`.  Hence every nonempty open patch in a finite mass-coordinate
space which contains a point strictly inside that cube has positive iid
probability.  This is the finite-product support statement needed to lift a
slice witness to a genuine all-coordinate random-mass event.
-/

namespace ArchonPhysics.FiniteMassLawOpenPatch

open ArchonPhysics
open MeasureTheory ProbabilityTheory Set
open RandomEnsemble

noncomputable section

/-- Every open neighbourhood of a point in the interior of the finite mass
cube has strictly positive canonical finite-product mass. -/
theorem finiteMassLaw_pos_of_isOpen_of_mem_interior
    {N : Nat} {patch : Set (Fin N → Real)}
    (hpatch : IsOpen patch) (x : Fin N → Real) (hx : x ∈ patch)
    (hxInterior : ∀ i, x i ∈ Ioo massLower massUpper) :
    0 < finiteMassLaw N patch := by
  obtain ⟨coordinatePatch, hcoordinatePatch, hsubset⟩ :=
    (isOpen_pi_iff'.mp hpatch) x hx
  let interiorCoordinatePatch : Fin N → Set Real := fun i ↦
    coordinatePatch i ∩ Ioo massLower massUpper
  have hopen (i : Fin N) : IsOpen (interiorCoordinatePatch i) :=
    (hcoordinatePatch i).1.inter isOpen_Ioo
  have hxCoordinate (i : Fin N) : x i ∈ interiorCoordinatePatch i :=
    ⟨(hcoordinatePatch i).2, hxInterior i⟩
  have hrectangleSubset :
      Set.univ.pi interiorCoordinatePatch ⊆ patch := by
    apply hsubset.trans'
    intro y hy i _hi
    exact (hy i (Set.mem_univ i)).1
  have hcoordinatePositive (i : Fin N) :
      0 < massCoordinateLaw (interiorCoordinatePatch i) := by
    have hmeasurable : MeasurableSet (interiorCoordinatePatch i) :=
      (hopen i).measurableSet
    have hinside : interiorCoordinatePatch i ⊆ massSupport := by
      intro y hy
      exact ⟨hy.2.1.le, hy.2.2.le⟩
    rw [massCoordinateLaw,
      ProbabilityTheory.cond_apply' hmeasurable volume,
      inter_eq_right.mpr hinside]
    exact ENNReal.mul_pos_iff.2
      ⟨ENNReal.inv_pos.mpr (by
          simp [massSupport, massLower, massUpper, Real.volume_Icc]),
        (hopen i).measure_pos volume ⟨x i, hxCoordinate i⟩⟩
  have hrectanglePositive :
      0 < finiteMassLaw N (Set.univ.pi interiorCoordinatePatch) := by
    rw [finiteMassLaw, Measure.pi_pi]
    exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _hi ↦ (hcoordinatePositive i).ne')
  exact hrectanglePositive.trans_le (measure_mono hrectangleSubset)

end

end ArchonPhysics.FiniteMassLawOpenPatch
