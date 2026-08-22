import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2TwistedFiberVolumeV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Volume preservation of the WZ2 twisted fiber chart

The fiber chart for `pi_f(x,y,z) = (x + f(z)y,z)` is triangular.  This
module proves that it preserves Euclidean volume by decomposing it into:

1. a two-dimensional translation shear at fixed `z`;
2. a measurable skew product over the remaining coordinates;
3. measure-preserving coordinate permutations and the canonical
   product-coordinate equivalence with `EuclideanSpace R (Fin 3)`.

This is the change-of-variables producer required after the slice-retention
module.  Volume preservation is proved, not supplied as a callback.
-/

private abbrev realVolume : Measure Real := volume

/-- The fixed-`z` planar shear in `(u,y)` coordinates. -/
def fixedZShear (f : Real -> Real) (z : Real) (p : Real × Real) :
    Real × Real :=
  (p.1 - f z * p.2, p.2)

/-- The same fixed-`z` shear with the invariant coordinate listed first. -/
private def fixedZShearFiberFirst
    (f : Real -> Real) (z : Real) (p : Real × Real) : Real × Real :=
  (p.1, p.2 - f z * p.1)

/-- At every fixed `z`, the planar translation shear preserves product
Lebesgue measure. -/
theorem fixedZShear_measurePreserving (f : Real -> Real) (z : Real) :
    MeasurePreserving (fixedZShear f z)
      (realVolume.prod realVolume) (realVolume.prod realVolume) := by
  have hfiberFirst :
      MeasurePreserving (fixedZShearFiberFirst f z)
        (realVolume.prod realVolume) (realVolume.prod realVolume) := by
    refine MeasurePreserving.skew_product
      (g := fun y u => u - f z * y)
      (MeasurePreserving.id realVolume) ?_ ?_
    · fun_prop
    · filter_upwards with y
      simpa [sub_eq_add_neg] using
        (measurePreserving_add_right realVolume (-(f z * y))).map_eq
  have hswap :
      MeasurePreserving (Prod.swap : Real × Real -> Real × Real)
        (realVolume.prod realVolume) (realVolume.prod realVolume) :=
    Measure.measurePreserving_swap
  have h := hswap.comp (hfiberFirst.comp hswap)
  convert h using 1
  ext p <;> rfl

/-- Put the invariant base `(y,z)` before the translated fiber coordinate
`u`. -/
def fiberBasePermutation (q : (Real × Real) × Real) :
    (Real × Real) × Real :=
  ((q.2, q.1.2), q.1.1)

/-- The cyclic coordinate permutation is product-volume preserving. -/
theorem fiberBasePermutation_measurePreserving :
    MeasurePreserving fiberBasePermutation
      ((realVolume.prod realVolume).prod realVolume)
      ((realVolume.prod realVolume).prod realVolume) := by
  have hassoc :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc : (Real × Real) × Real ≃ᵐ
          Real × (Real × Real))
        ((realVolume.prod realVolume).prod realVolume)
        (realVolume.prod (realVolume.prod realVolume)) :=
    measurePreserving_prodAssoc realVolume realVolume realVolume
  have hinnerSwap :
      MeasurePreserving (Prod.map id Prod.swap)
        (realVolume.prod (realVolume.prod realVolume))
        (realVolume.prod (realVolume.prod realVolume)) :=
    (MeasurePreserving.id realVolume).prod
      (Measure.measurePreserving_swap (μ := realVolume) (ν := realVolume))
  have houterSwap :
      MeasurePreserving Prod.swap
        (realVolume.prod (realVolume.prod realVolume))
        ((realVolume.prod realVolume).prod realVolume) :=
    Measure.measurePreserving_swap
  have h := houterSwap.comp (hinnerSwap.comp hassoc)
  convert h using 1
  ext q <;> rfl

/-- The full triangular shear, with base `(y,z)` and fiber `u`. -/
def baseFiberShear (f : Real -> Real) (q : (Real × Real) × Real) :
    (Real × Real) × Real :=
  (q.1, q.2 - f q.1.2 * q.1.1)

/-- Measurable dependence of the translation amount on `(y,z)` preserves
three-dimensional product volume by the skew-product theorem. -/
theorem baseFiberShear_measurePreserving
    (f : Real -> Real) (hf : Measurable f) :
    MeasurePreserving (baseFiberShear f)
      ((realVolume.prod realVolume).prod realVolume)
      ((realVolume.prod realVolume).prod realVolume) := by
  refine MeasurePreserving.skew_product
    (g := fun q u => u - f q.2 * q.1)
    (MeasurePreserving.id (realVolume.prod realVolume)) ?_ ?_
  · exact measurable_snd.sub
      ((hf.comp (measurable_snd.comp measurable_fst)).mul
        (measurable_fst.comp measurable_fst))
  · filter_upwards with q
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right realVolume
        (-(f q.2 * q.1))).map_eq

/-- Canonical product coordinates `(x,(y,z))` on ambient `Space`. -/
def spaceCoordinates (p : Space) : Real × (Real × Real) :=
  (p 0, (p 1, p 2))

/-- Pack canonical product coordinates into ambient `Space`. -/
def coordinatesToSpace (q : Real × (Real × Real)) : Space :=
  point3 q.1 q.2.1 q.2.2

/-- The explicit coordinate maps are inverse. -/
theorem coordinatesToSpace_spaceCoordinates (p : Space) :
    coordinatesToSpace (spaceCoordinates p) = p := by
  ext i
  fin_cases i <;> simp [coordinatesToSpace, spaceCoordinates, point3]

/-- The explicit coordinate maps are inverse in the other direction. -/
theorem spaceCoordinates_coordinatesToSpace (q : Real × (Real × Real)) :
    spaceCoordinates (coordinatesToSpace q) = q := by
  rcases q with ⟨x, y, z⟩
  simp [coordinatesToSpace, spaceCoordinates, point3]

/-- Product coordinates as the canonical composition of the `WithLp`,
`Fin 3`, and `Fin 2` measurable equivalences. -/
def spaceCoordinateMeasurableEquiv : Space ≃ᵐ Real × (Real × Real) :=
  (MeasurableEquiv.toLp 2 (Fin 3 -> Real)).symm |>.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) (0 : Fin 3)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Real)
        (MeasurableEquiv.piFinTwo fun _ : Fin 2 => Real)))

/-- The canonical measurable equivalence has the advertised explicit
coordinate formula. -/
theorem spaceCoordinateMeasurableEquiv_apply (p : Space) :
    spaceCoordinateMeasurableEquiv p = spaceCoordinates p := by
  ext <;> rfl

/-- The canonical product-coordinate equivalence preserves volume. -/
theorem spaceCoordinates_measurePreserving :
    MeasurePreserving spaceCoordinates volume
      (realVolume.prod (realVolume.prod realVolume)) := by
  have hlp :
      MeasurePreserving (@WithLp.ofLp 2 (Fin 3 -> Real)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have hsucc :=
    volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => Real) (0 : Fin 3)
  have htwo :=
    volume_preserving_piFinTwo (fun _ : Fin 2 => Real)
  have hprod := (MeasurePreserving.id realVolume).prod htwo
  have h := hprod.comp (hsucc.comp hlp)
  have hcanonical :
      (spaceCoordinateMeasurableEquiv : Space -> Real × (Real × Real)) =
        (Prod.map id (MeasurableEquiv.piFinTwo fun _ : Fin 2 => Real) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) (0 : Fin 3)) ∘
            (@WithLp.ofLp 2 (Fin 3 -> Real))) := by
    funext p
    rfl
  have h' :
      MeasurePreserving spaceCoordinateMeasurableEquiv volume
        (realVolume.prod (realVolume.prod realVolume)) := by
    rw [hcanonical]
    simpa only [Measure.volume_eq_prod] using h
  rw [show spaceCoordinates = spaceCoordinateMeasurableEquiv from
    funext fun p => (spaceCoordinateMeasurableEquiv_apply p).symm]
  exact h'

/-- Packing product coordinates into `Space` also preserves volume. -/
theorem coordinatesToSpace_measurePreserving :
    MeasurePreserving coordinatesToSpace
      (realVolume.prod (realVolume.prod realVolume)) volume := by
  have hforward :
      MeasurePreserving spaceCoordinateMeasurableEquiv volume
        (realVolume.prod (realVolume.prod realVolume)) := by
    have heq :
        (spaceCoordinateMeasurableEquiv : Space -> Real × (Real × Real)) =
          spaceCoordinates :=
      funext spaceCoordinateMeasurableEquiv_apply
    rw [heq]
    exact spaceCoordinates_measurePreserving
  have hinverse := MeasurePreserving.symm spaceCoordinateMeasurableEquiv hforward
  have hinverseFormula :
      coordinatesToSpace = (spaceCoordinateMeasurableEquiv.symm :
        Real × (Real × Real) -> Space) := by
    funext q
    apply spaceCoordinateMeasurableEquiv.injective
    rw [MeasurableEquiv.apply_symm_apply]
    exact (spaceCoordinateMeasurableEquiv_apply (coordinatesToSpace q)).trans
      (spaceCoordinates_coordinatesToSpace q)
  rw [hinverseFormula]
  exact hinverse

/-- The explicit WZ2 twisted fiber chart preserves Euclidean volume for every
measurable slope function `f`. -/
theorem twistedFiberChart_measurePreserving
    (f : Real -> Real) (hf : Measurable f) :
    MeasurePreserving (twistedFiberChart f)
      (volume : Measure (ProjectionSpace × Real)) volume := by
  have hperm := fiberBasePermutation_measurePreserving
  have hshear := baseFiberShear_measurePreserving f hf
  have hswap :
      MeasurePreserving Prod.swap
        ((realVolume.prod realVolume).prod realVolume)
        (realVolume.prod (realVolume.prod realVolume)) :=
    Measure.measurePreserving_swap
  have h := coordinatesToSpace_measurePreserving.comp
    (hswap.comp (hshear.comp hperm))
  have hfun :
      twistedFiberChart f =
        coordinatesToSpace ∘ Prod.swap ∘ baseFiberShear f ∘
          fiberBasePermutation := by
    funext q
    rfl
  rw [hfun]
  simpa only [Measure.volume_eq_prod] using h

#print axioms fixedZShear_measurePreserving
#print axioms fiberBasePermutation_measurePreserving
#print axioms baseFiberShear_measurePreserving
#print axioms spaceCoordinates_measurePreserving
#print axioms coordinatesToSpace_measurePreserving
#print axioms twistedFiberChart_measurePreserving

end

end FamilyStickyWZ2TwistedFiberVolumeV1
