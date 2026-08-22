import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace FamilyStickyLatticeBoxPointCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Explicit finite coordinate lattice for one frame box

For a box-specific orthonormal frame, take finitely many lattice sites in
each coordinate, with spacing strictly larger than the corresponding full
side length.  No two distinct sites can translate the same ambient point
into the box.  This is the elementary finite-grid point-count input behind
the appendix incidence estimate; it contains no probability conclusion.
-/

/-- Three-coordinate finite lattice sites with a separately chosen number
of sites in each frame direction. -/
abbrev BoxLatticeSites (siteCount : Fin 3 -> Nat) :=
  forall i, Fin (siteCount i)

/-- The actual ambient translation vector of a finite box lattice site. -/
def boxLatticeVector (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat} (g : BoxLatticeSites siteCount) : Space :=
  ∑ i, (((g i : Nat) : Real) * (spacing i : Real)) • B.frame i

@[simp] theorem inner_boxLatticeVector
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat} (g : BoxLatticeSites siteCount) (i : Fin 3) :
    ⟪B.frame i, boxLatticeVector B spacing g⟫_Real =
      ((g i : Nat) : Real) * (spacing i : Real) := by
  simp [boxLatticeVector, inner_sum, real_inner_smul_right,
    B.frame.inner_eq_ite]

/-- A real interval of width `width` cannot contain two points from a
one-dimensional nonnegative integer lattice whose spacing exceeds `width`. -/
theorem nat_eq_of_abs_cast_sub_mul_le
    {a b : Nat} {spacing width : Real}
    (hwidth : 0 <= width) (hspacing : width < spacing)
    (hab : |((a : Real) - (b : Real)) * spacing| <= width) :
    a = b := by
  by_contra hne
  have hspacingPos : 0 < spacing := hwidth.trans_lt hspacing
  rcases Nat.lt_or_gt_of_ne hne with hablt | hbalt
  · have habcast : (a : Real) + 1 <= (b : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hablt)
    have hgap : (1 : Real) <= (b : Real) - (a : Real) := by linarith
    have habcastLe : (a : Real) <= (b : Real) := by exact_mod_cast Nat.le_of_lt hablt
    have hsign : ((a : Real) - (b : Real)) * spacing <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr habcastLe) hspacingPos.le
    rw [abs_of_nonpos hsign] at hab
    have hmul : spacing <= ((b : Real) - (a : Real)) * spacing := by
      nlinarith
    nlinarith
  · have hbacast : (b : Real) + 1 <= (a : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hbalt)
    have hgap : (1 : Real) <= (a : Real) - (b : Real) := by linarith
    have hbacastLe : (b : Real) <= (a : Real) := by exact_mod_cast Nat.le_of_lt hbalt
    have hsign : 0 <= ((a : Real) - (b : Real)) * spacing :=
      mul_nonneg (sub_nonneg.mpr hbacastLe) hspacingPos.le
    rw [abs_of_nonneg hsign] at hab
    have hmul : spacing <= ((a : Real) - (b : Real)) * spacing := by
      nlinarith
    nlinarith

/-- If two sites translate the same point into the frame box, the sites are
equal.  This is the coordinate separation statement used for point counts. -/
theorem boxLatticeSites_eq_of_add_mem_carrier
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat}
    (hspacing : forall i, B.side i < spacing i)
    (x : Space) (g h : BoxLatticeSites siteCount)
    (hg : x + boxLatticeVector B spacing g ∈ B.carrier)
    (hh : x + boxLatticeVector B spacing h ∈ B.carrier) :
    g = h := by
  funext i
  apply Fin.ext
  apply nat_eq_of_abs_cast_sub_mul_le
    (show (0 : Real) <= (B.side i : Real) by positivity)
    (by exact_mod_cast hspacing i)
  have hgcoord := B.centeredCoordinate_abs_le_halfSide hg i
  have hhcoord := B.centeredCoordinate_abs_le_halfSide hh i
  have hdiff :
      |⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
          ⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real| <=
        (B.side i : Real) := by
    calc
      |⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
          ⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real| =
          |(⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
              ⟪B.frame i, B.center⟫_Real) -
            (⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real -
              ⟪B.frame i, B.center⟫_Real)| := by ring_nf
      _ <= |⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
              ⟪B.frame i, B.center⟫_Real| +
            |⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real -
              ⟪B.frame i, B.center⟫_Real| := abs_sub _ _
      _ <= (B.side i : Real) / 2 + (B.side i : Real) / 2 :=
        add_le_add hgcoord hhcoord
      _ = (B.side i : Real) := by ring
  calc
    |(((g i : Nat) : Real) - ((h i : Nat) : Real)) * (spacing i : Real)| =
        |⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
          ⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real| := by
      rw [inner_add_right, inner_add_right, inner_boxLatticeVector,
        inner_boxLatticeVector]
      ring_nf
    _ <= (B.side i : Real) := hdiff

/-- Literal number of finite lattice sites translating a fixed point into
the box. -/
def boxPointHitCount
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat} (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun g : BoxLatticeSites siteCount =>
    x + boxLatticeVector B spacing g ∈ B.carrier).card

/-- Literal finite coordinate count: at most one site translates a fixed
point into the box. -/
theorem boxPointHitCount_le_one
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat}
    (hspacing : forall i, B.side i < spacing i) (x : Space) :
    boxPointHitCount B spacing (siteCount := siteCount) x <= 1 := by
  classical
  unfold boxPointHitCount
  rw [Finset.card_le_one]
  intro g hg h hh
  exact boxLatticeSites_eq_of_add_mem_carrier B spacing hspacing x g h
    (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hh).2

#print axioms inner_boxLatticeVector
#print axioms nat_eq_of_abs_cast_sub_mul_le
#print axioms boxLatticeSites_eq_of_add_mem_carrier
#print axioms boxPointHitCount_le_one

end


end FamilyStickyLatticeBoxPointCountV1
