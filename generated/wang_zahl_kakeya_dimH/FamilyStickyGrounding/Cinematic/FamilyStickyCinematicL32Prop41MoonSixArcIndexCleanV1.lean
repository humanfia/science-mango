import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1

noncomputable section

/-!
# Canonical `Fin 2 × Fin 3` indexing of the six actual moon arcs

This is the finite bridge to the rotation-system obstruction.  The index map
is proved injective from literal unordered-pair equality and the genuine
non-diagonal pair carrier; no geometric non-overlap or forbidden-triple
conclusion is assumed.
-/

def moonHost
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (_C : MoonFiveCurveConfiguration D items leftHost rightHost x y z) :
    Fin 2 -> FirstGenerationCurve curves :=
  Fin.cases leftHost (fun _ => rightHost)

def moonNeighbor
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (_C : MoonFiveCurveConfiguration D items leftHost rightHost x y z) :
    Fin 3 -> FirstGenerationCurve curves :=
  Fin.cases x (fun i => Fin.cases y (fun _ => z) i)

noncomputable def moonSixArc
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z)
    (i : Fin 2) (j : Fin 3) :
    MoonPositiveSideArc D items (moonHost C i) (moonNeighbor C j) :=
  Fin.cases
    (Fin.cases C.leftX
      (fun j' => Fin.cases C.leftY (fun _ => C.leftZ) j') j)
    (fun _ => Fin.cases C.rightX
      (fun j' => Fin.cases C.rightY (fun _ => C.rightZ) j') j) i

def moonSixPair
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z)
    (e : Fin 2 × Fin 3) : FirstGenerationCurvePair curves :=
  (moonSixArc C e.1 e.2).pair

theorem moonPositiveSideArc_host_ne_neighbor
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc D items host neighbor) : host ≠ neighbor := by
  intro heq
  apply arc.pair.2
  rw [arc.pair_eq, Sym2.mk_isDiag_iff]
  exact heq

theorem moonSixPair_pair_eq
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z)
    (e : Fin 2 × Fin 3) :
    (moonSixPair C e).1 = s(moonHost C e.1, moonNeighbor C e.2) :=
  (moonSixArc C e.1 e.2).pair_eq

theorem moonHost_injective
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z) :
    Function.Injective (moonHost C) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [moonHost] at hij ⊢
  · exact (C.host_ne hij).elim
  · exact (C.host_ne hij.symm).elim

theorem moonNeighbor_injective
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z) :
    Function.Injective (moonNeighbor C) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [moonNeighbor] at hij ⊢
  · exact (C.x_ne_y hij).elim
  · exact (C.z_ne_x hij.symm).elim
  · exact (C.x_ne_y hij.symm).elim
  · exact (C.y_ne_z hij).elim
  · exact (C.z_ne_x hij).elim
  · exact (C.y_ne_z hij.symm).elim

theorem moonHost_ne_neighbor
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z)
    (i : Fin 2) (j : Fin 3) : moonHost C i ≠ moonNeighbor C j :=
  moonPositiveSideArc_host_ne_neighbor (moonSixArc C i j)

theorem moonSixPair_injective
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z) :
    Function.Injective (moonSixPair C) := by
  intro e f hef
  have hpairs : s(moonHost C e.1, moonNeighbor C e.2) =
      s(moonHost C f.1, moonNeighbor C f.2) := by
    rw [← moonSixPair_pair_eq C e, ← moonSixPair_pair_eq C f]
    exact congrArg Subtype.val hef
  rw [Sym2.eq_iff] at hpairs
  rcases hpairs with hpairs | hpairs
  · exact Prod.ext
      (moonHost_injective C hpairs.1)
      (moonNeighbor_injective C hpairs.2)
  · exact (moonHost_ne_neighbor C e.1 f.2 hpairs.1).elim

theorem moonSixPair_mem_items
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration D items leftHost rightHost x y z)
    (e : Fin 2 × Fin 3) : moonSixPair C e ∈ items :=
  (moonSixArc C e.1 e.2).pair_mem

#print axioms moonHost
#print axioms moonNeighbor
#print axioms moonSixArc
#print axioms moonSixPair
#print axioms moonPositiveSideArc_host_ne_neighbor
#print axioms moonSixPair_injective
#print axioms moonSixPair_mem_items

end

end FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
