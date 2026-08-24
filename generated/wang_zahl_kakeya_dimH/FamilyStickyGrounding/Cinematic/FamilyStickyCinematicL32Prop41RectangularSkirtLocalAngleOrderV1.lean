import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtLocalAngleOrderV1

open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

noncomputable section

/-!
# Local angular order at a graph crossing

The oriented graph arc is parametrised by increasing `theta`, hence its
tangent is `(g'(theta), 1)`.  The determinant from the host tangent to a
neighbor tangent is exactly `host' - neighbor'`.  This is the faithful
secondary key at a common loop-entry parameter.  In particular, A3 implies
that two distinct neighbors through the same host point have distinct keys;
no general-position exclusion of triple graph intersections is needed.
-/

variable {curve : Type*} [DecidableEq curve]
variable {curves : Finset curve}

/-- The tangent of an actual graph arc with its increasing-parameter
orientation. -/
def orientedGraphTangent
    (first : curve -> Real -> Real) (c : curve) (theta : Real) : Real × Real :=
  (first c theta, 1)

/-- The standard oriented area form on the plane. -/
def planeDet (u v : Real × Real) : Real :=
  u.1 * v.2 - u.2 * v.1

/-- Signed local counterclockwise angle key of a neighbor ray relative to
the oriented host graph ray.  On the upper half-plane tangent chart this
orders rays exactly by their local cyclic angle around the host tangent. -/
def graphSideEntryLocalAngleKey
    (first : curve -> Real -> Real) (host neighbor : curve)
    (theta : Real) : Real :=
  planeDet (orientedGraphTangent first host theta)
    (orientedGraphTangent first neighbor theta)

omit [DecidableEq curve] in
theorem graphSideEntryLocalAngleKey_eq_first_sub
    (first : curve -> Real -> Real) (host neighbor : curve)
    (theta : Real) :
    graphSideEntryLocalAngleKey first host neighbor theta =
      first host theta - first neighbor theta := by
  simp [graphSideEntryLocalAngleKey, planeDet, orientedGraphTangent]

/-- The literal local side-entry order, expressed by the oriented tangent
determinant rather than by an arbitrary finite enumeration. -/
def GraphSideEntryLocallyBefore
    (first : curve -> Real -> Real) (host left right : curve)
    (theta : Real) : Prop :=
  planeDet (orientedGraphTangent first host theta)
      (orientedGraphTangent first left theta) <
    planeDet (orientedGraphTangent first host theta)
      (orientedGraphTangent first right theta)

omit [DecidableEq curve] in
theorem graphSideEntryLocallyBefore_iff_angleKey_lt
    (first : curve -> Real -> Real) (host left right : curve)
    (theta : Real) :
    GraphSideEntryLocallyBefore first host left right theta ↔
      graphSideEntryLocalAngleKey first host left theta <
        graphSideEntryLocalAngleKey first host right theta := by
  rfl

omit [DecidableEq curve] in
theorem graphSideEntryLocallyBefore_iff_derivative_difference_lt
    (first : curve -> Real -> Real) (host left right : curve)
    (theta : Real) :
    GraphSideEntryLocallyBefore first host left right theta ↔
      first host theta - first left theta <
        first host theta - first right theta := by
  simp [GraphSideEntryLocallyBefore, planeDet, orientedGraphTangent]

/-- A3 separates the local angular keys of any two distinct neighbors that
meet the same host at the same graph point.  Triple crossings are therefore
allowed: only tangential coincidence of the two neighbor rays is excluded. -/
theorem graphSideEntryLocalAngleKey_ne_of_A3
    (graph first : curve -> Real -> Real) (A B : Real)
    (hA3 : NoTangentialGraphIntersections curves graph first A B)
    {host left right : curve} (hleft : left ∈ curves)
    (hright : right ∈ curves) (hlr : left ≠ right)
    {theta : Real} (htheta : theta ∈ Icc A B)
    (hhostLeft : graph host theta = graph left theta)
    (hhostRight : graph host theta = graph right theta) :
    graphSideEntryLocalAngleKey first host left theta ≠
      graphSideEntryLocalAngleKey first host right theta := by
  intro hkey
  have hfirst : first left theta = first right theta := by
    rw [graphSideEntryLocalAngleKey_eq_first_sub,
      graphSideEntryLocalAngleKey_eq_first_sub] at hkey
    linarith
  have hgraph : graph left theta = graph right theta :=
    hhostLeft.symm.trans hhostRight
  exact hA3 left hleft right hright hlr theta htheta ⟨hgraph, hfirst⟩

/-- At a shared graph point A3 makes the local order strict in one of the
two directions. -/
theorem graphSideEntryLocallyBefore_or_reverse_of_A3
    (graph first : curve -> Real -> Real) (A B : Real)
    (hA3 : NoTangentialGraphIntersections curves graph first A B)
    {host left right : curve} (hleft : left ∈ curves)
    (hright : right ∈ curves) (hlr : left ≠ right)
    {theta : Real} (htheta : theta ∈ Icc A B)
    (hhostLeft : graph host theta = graph left theta)
    (hhostRight : graph host theta = graph right theta) :
    GraphSideEntryLocallyBefore first host left right theta \/
      GraphSideEntryLocallyBefore first host right left theta := by
  have hne := graphSideEntryLocalAngleKey_ne_of_A3 graph first A B hA3
    hleft hright hlr htheta hhostLeft hhostRight
  exact lt_or_gt_of_ne hne

#print axioms orientedGraphTangent
#print axioms planeDet
#print axioms graphSideEntryLocalAngleKey
#print axioms graphSideEntryLocalAngleKey_eq_first_sub
#print axioms GraphSideEntryLocallyBefore
#print axioms graphSideEntryLocallyBefore_iff_angleKey_lt
#print axioms graphSideEntryLocallyBefore_iff_derivative_difference_lt
#print axioms graphSideEntryLocalAngleKey_ne_of_A3
#print axioms graphSideEntryLocallyBefore_or_reverse_of_A3

end

end FamilyStickyCinematicL32Prop41RectangularSkirtLocalAngleOrderV1
