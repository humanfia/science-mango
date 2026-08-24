import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1

noncomputable section

/-!
# Honest five-curve carrier extracted from a moon forbidden triple

A forbidden triple is used only as the assumption to be contradicted.  This
module mechanically exposes its six literal selected-pair witnesses and the
positive host side of every moon.  It contains no no-triple, intersection-
reverse, or equivalent geometric callback.
-/

/-- One literal selected moon incident to a specified host and neighbor,
together with the positive host side forced by the computed moon class. -/
structure MoonPositiveSideArc
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (host neighbor : FirstGenerationCurve curves) where
  pair : FirstGenerationCurvePair curves
  pair_mem : pair ∈ items
  pair_eq : pair.1 = s(host, neighbor)
  assigned : selectedLensAssignedTo D.toSelectedFixedSlotLensGeometry
    ProperLensKind.moonFace host pair
  host_positive :
    (host = D.firstCurve pair ∧ firstSidePositive
      D.toSelectedFixedSlotLensGeometry pair) ∨
    (host = D.secondCurve pair ∧ secondSidePositive
      D.toSelectedFixedSlotLensGeometry pair)

/-- Two host curves and three common neighbors give the six literal positive
moon sides used in the Marcus--Tardos five-pseudocircle argument. -/
structure MoonFiveCurveConfiguration
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (leftHost rightHost x y z : FirstGenerationCurve curves) where
  host_ne : leftHost ≠ rightHost
  x_ne_y : x ≠ y
  y_ne_z : y ≠ z
  z_ne_x : z ≠ x
  leftX : MoonPositiveSideArc D items leftHost x
  leftY : MoonPositiveSideArc D items leftHost y
  leftZ : MoonPositiveSideArc D items leftHost z
  rightX : MoonPositiveSideArc D items rightHost x
  rightY : MoonPositiveSideArc D items rightHost y
  rightZ : MoonPositiveSideArc D items rightHost z
  cyclicLeft : CyclicallyOrdered
    (localAngleSelectedLensNeighborSequence D items
      ProperLensKind.moonFace leftHost) x y z
  cyclicRight : CyclicallyOrdered
    (localAngleSelectedLensNeighborSequence D items
      ProperLensKind.moonFace rightHost) x y z

/-- A literal moon-neighbor relation automatically produces the positive
side arc; positivity is not a source field. -/
noncomputable def moonPositiveSideArcOfRelation
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (host neighbor : FirstGenerationCurve curves)
    (hrelation : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace host neighbor) :
    MoonPositiveSideArc D items host neighbor := by
  classical
  let p : FirstGenerationCurvePair curves := Classical.choose hrelation
  have hp := Classical.choose_spec hrelation
  have hhost : selectedLensHost D.toSelectedFixedSlotLensGeometry p = host := by
    change selectedLensHost D.toSelectedFixedSlotLensGeometry
      (Classical.choose hrelation) = host
    simpa [selectedLensAssignedTo] using hp.2.1.2
  have hpositive := selectedLensHost_positive_of_moonFace
    D.toSelectedFixedSlotLensGeometry p hp.2.1.1
  refine
    { pair := p
      pair_mem := hp.1
      pair_eq := hp.2.2
      assigned := hp.2.1
      host_positive := ?_ }
  rcases hpositive with hfirst | hsecond
  · exact Or.inl ⟨hhost.symm.trans hfirst.1, hfirst.2⟩
  · exact Or.inr ⟨hhost.symm.trans hsecond.1, hsecond.2⟩

/-- Mechanical six-arc producer from a literal common cyclic triple. -/
noncomputable def moonFiveCurveConfigurationOfSameCyclicTriple
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (leftHost rightHost x y z : FirstGenerationCurve curves)
    (hhost : leftHost ≠ rightHost)
    (htriple : SameCyclicTriple
      (localAngleSelectedLensNeighborSequence D items
        ProperLensKind.moonFace leftHost)
      (localAngleSelectedLensNeighborSequence D items
        ProperLensKind.moonFace rightHost) x y z) :
    MoonFiveCurveConfiguration D items leftHost rightHost x y z := by
  classical
  have hxy := htriple.1
  have hyz := htriple.2.1
  have hzx := htriple.2.2.1
  have hx := htriple.2.2.2.1
  have hy := htriple.2.2.2.2.1
  have hz := htriple.2.2.2.2.2.1
  have hcyclicLeft := htriple.2.2.2.2.2.2.1
  have hcyclicRight := htriple.2.2.2.2.2.2.2
  have hxmem := Finset.mem_inter.mp hx
  have hymem := Finset.mem_inter.mp hy
  have hzmem := Finset.mem_inter.mp hz
  have hleftX : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace leftHost x :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace leftHost x).mp hxmem.1
  have hleftY : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace leftHost y :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace leftHost y).mp hymem.1
  have hleftZ : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace leftHost z :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace leftHost z).mp hzmem.1
  have hrightX : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace rightHost x :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace rightHost x).mp hxmem.2
  have hrightY : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace rightHost y :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace rightHost y).mp hymem.2
  have hrightZ : localAngleSelectedLensNeighborRelation D items
      ProperLensKind.moonFace rightHost z :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      D items ProperLensKind.moonFace rightHost z).mp hzmem.2
  exact
    { host_ne := hhost
      x_ne_y := hxy
      y_ne_z := hyz
      z_ne_x := hzx
      leftX := moonPositiveSideArcOfRelation D items leftHost x hleftX
      leftY := moonPositiveSideArcOfRelation D items leftHost y hleftY
      leftZ := moonPositiveSideArcOfRelation D items leftHost z hleftZ
      rightX := moonPositiveSideArcOfRelation D items rightHost x hrightX
      rightY := moonPositiveSideArcOfRelation D items rightHost y hrightY
      rightZ := moonPositiveSideArcOfRelation D items rightHost z hrightZ
      cyclicLeft := hcyclicLeft
      cyclicRight := hcyclicRight }

#print axioms MoonPositiveSideArc
#print axioms MoonFiveCurveConfiguration
#print axioms moonPositiveSideArcOfRelation
#print axioms moonFiveCurveConfigurationOfSameCyclicTriple

end

end FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
