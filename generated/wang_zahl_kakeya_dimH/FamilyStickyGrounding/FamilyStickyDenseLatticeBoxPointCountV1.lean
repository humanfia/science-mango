import FamilyStickyGrounding.FamilyStickyLatticeBoxPointCountV1

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace FamilyStickyDenseLatticeBoxPointCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyLatticeBoxPointCountV1

noncomputable section

/-!
# Dense finite lattice interval counts for a frame box

The coarse `fibre <= 1` lattice required spacing larger than a full test-box
side, which is incompatible with small translations when a test has a long
axis.  Here the spacing is arbitrary and the hit fibre is injected into
coordinate residues.  If `side_i < budget_i * spacing_i`, then each coordinate
needs at most `budget_i` residue classes, so the literal three-dimensional hit
count is at most `prod_i budget_i`.

The canonical budget is `ceil(side_i / spacing_i) + 1`.  Thus no interval-count
or point-hit estimate is accepted as a callback.
-/

/-- Equal residues modulo a positive budget, combined with an interval-width
bound, force equality of two lattice indices. -/
theorem nat_eq_of_mod_eq_of_abs_cast_sub_mul_le
    {a b budget : Nat} {spacing width : Real}
    (_hbudget : 0 < budget) (hwidth : 0 <= width)
    (hcover : width < (budget : Real) * spacing)
    (hmod : a % budget = b % budget)
    (hab : |((a : Real) - (b : Real)) * spacing| <= width) :
    a = b := by
  by_contra hne
  have hspacingPos : 0 < spacing := by
    by_contra hs
    have hsnonpos : spacing <= 0 := le_of_not_gt hs
    have : (budget : Real) * spacing <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hsnonpos
    linarith
  have hmodeq : Nat.ModEq budget a b := hmod
  rcases Nat.lt_or_gt_of_ne hne with hablt | hbalt
  · have hdiv : budget ∣ b - a :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hablt)).mp hmodeq
    have hgapNat : budget <= b - a :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hablt) hdiv
    have hgapAdd : budget + a <= b := by omega
    have hgapCast : (budget : Real) + (a : Real) <= (b : Real) := by
      exact_mod_cast hgapAdd
    have hgap : (budget : Real) <= (b : Real) - (a : Real) := by
      linarith
    have hsign : ((a : Real) - (b : Real)) * spacing <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt hablt)) hspacingPos.le
    rw [abs_of_nonpos hsign] at hab
    have hmul : (budget : Real) * spacing <=
        ((b : Real) - (a : Real)) * spacing :=
      mul_le_mul_of_nonneg_right hgap hspacingPos.le
    nlinarith
  · have hmodeq' : Nat.ModEq budget b a := hmodeq.symm
    have hdiv : budget ∣ a - b :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hbalt)).mp hmodeq'
    have hgapNat : budget <= a - b :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hbalt) hdiv
    have hgapAdd : budget + b <= a := by omega
    have hgapCast : (budget : Real) + (b : Real) <= (a : Real) := by
      exact_mod_cast hgapAdd
    have hgap : (budget : Real) <= (a : Real) - (b : Real) := by
      linarith
    have hsign : 0 <= ((a : Real) - (b : Real)) * spacing :=
      mul_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hbalt))
        hspacingPos.le
    rw [abs_of_nonneg hsign] at hab
    have hmul : (budget : Real) * spacing <=
        ((a : Real) - (b : Real)) * spacing :=
      mul_le_mul_of_nonneg_right hgap hspacingPos.le
    nlinarith

/-- Coordinate residues used to encode all possible dense-lattice hits. -/
abbrev BoxLatticeResidues (hitBudget : Fin 3 -> Nat) :=
  forall i, Fin (hitBudget i)

/-- Residue vector of a dense three-coordinate lattice site. -/
def boxLatticeResidue
    {siteCount hitBudget : Fin 3 -> Nat}
    (hbudgetPos : forall i, 0 < hitBudget i)
    (g : BoxLatticeSites siteCount) : BoxLatticeResidues hitBudget :=
  fun i => ⟨(g i : Nat) % hitBudget i, Nat.mod_lt _ (hbudgetPos i)⟩

/-- Two points of a frame box differ by at most one full side length in each
frame coordinate. -/
theorem abs_inner_sub_inner_le_side
    (B : FrameBox) {y z : Space}
    (hy : y ∈ B.carrier) (hz : z ∈ B.carrier) (i : Fin 3) :
    |⟪B.frame i, y⟫_Real - ⟪B.frame i, z⟫_Real| <=
      (B.side i : Real) := by
  have hycoord := B.centeredCoordinate_abs_le_halfSide hy i
  have hzcoord := B.centeredCoordinate_abs_le_halfSide hz i
  calc
    |⟪B.frame i, y⟫_Real - ⟪B.frame i, z⟫_Real| =
        |(⟪B.frame i, y⟫_Real - ⟪B.frame i, B.center⟫_Real) -
          (⟪B.frame i, z⟫_Real - ⟪B.frame i, B.center⟫_Real)| := by
      ring_nf
    _ <= |⟪B.frame i, y⟫_Real - ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, z⟫_Real - ⟪B.frame i, B.center⟫_Real| :=
      abs_sub _ _
    _ <= (B.side i : Real) / 2 + (B.side i : Real) / 2 :=
      add_le_add hycoord hzcoord
    _ = (B.side i : Real) := by ring

/-- On the literal point-hit set, the coordinate residue vector is
injective. -/
theorem boxLatticeSites_eq_of_residue_eq_of_add_mem_carrier
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount hitBudget : Fin 3 -> Nat}
    (hbudgetPos : forall i, 0 < hitBudget i)
    (hcover : forall i,
      (B.side i : Real) < (hitBudget i : Real) * (spacing i : Real))
    (x : Space) (g h : BoxLatticeSites siteCount)
    (hg : x + boxLatticeVector B spacing g ∈ B.carrier)
    (hh : x + boxLatticeVector B spacing h ∈ B.carrier)
    (hresidue : boxLatticeResidue hbudgetPos g =
      boxLatticeResidue hbudgetPos h) :
    g = h := by
  funext i
  apply Fin.ext
  apply nat_eq_of_mod_eq_of_abs_cast_sub_mul_le
    (hbudgetPos i) (show (0 : Real) <= (B.side i : Real) by positivity)
    (hcover i)
  · have hi := congrFun hresidue i
    exact congrArg Fin.val hi
  · have hdiff := abs_inner_sub_inner_le_side B hg hh i
    calc
      |(((g i : Nat) : Real) - ((h i : Nat) : Real)) *
          (spacing i : Real)| =
          |⟪B.frame i, x + boxLatticeVector B spacing g⟫_Real -
            ⟪B.frame i, x + boxLatticeVector B spacing h⟫_Real| := by
        rw [inner_add_right, inner_add_right, inner_boxLatticeVector,
          inner_boxLatticeVector]
        ring_nf
      _ <= (B.side i : Real) := hdiff

/-- General dense-lattice finite interval count for one actual frame box. -/
theorem boxPointHitCount_le_prod_hitBudget
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount hitBudget : Fin 3 -> Nat}
    (hbudgetPos : forall i, 0 < hitBudget i)
    (hcover : forall i,
      (B.side i : Real) < (hitBudget i : Real) * (spacing i : Real))
    (x : Space) :
    boxPointHitCount B spacing (siteCount := siteCount) x <=
      ∏ i, hitBudget i := by
  classical
  let hits : Finset (BoxLatticeSites siteCount) :=
    Finset.univ.filter fun g => x + boxLatticeVector B spacing g ∈ B.carrier
  let residue : ↥hits -> BoxLatticeResidues hitBudget :=
    fun g => boxLatticeResidue hbudgetPos g.1
  have hresidue : Function.Injective residue := by
    intro g h heq
    apply Subtype.ext
    apply boxLatticeSites_eq_of_residue_eq_of_add_mem_carrier
      B spacing hbudgetPos hcover x
    · exact (Finset.mem_filter.mp g.2).2
    · exact (Finset.mem_filter.mp h.2).2
    · exact heq
  have hcard := Fintype.card_le_of_injective residue hresidue
  simpa only [boxPointHitCount, hits, Fintype.card_coe, BoxLatticeResidues,
    Fintype.card_pi, Fintype.card_fin] using hcard

/-- Canonical explicit coordinate hit budget: `ceil(side / spacing) + 1`. -/
def ceilHitBudget (B : FrameBox) (spacing : Fin 3 -> NNReal) (i : Fin 3) : Nat :=
  Nat.ceil ((B.side i : Real) / (spacing i : Real)) + 1

theorem ceilHitBudget_pos
    (B : FrameBox) (spacing : Fin 3 -> NNReal) (i : Fin 3) :
    0 < ceilHitBudget B spacing i := by
  simp [ceilHitBudget]

/-- Positive spacing makes the canonical ceiling budget cover the full side
length strictly. -/
theorem side_lt_ceilHitBudget_mul_spacing
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    (hspacing : forall i, 0 < spacing i) (i : Fin 3) :
    (B.side i : Real) <
      (ceilHitBudget B spacing i : Real) * (spacing i : Real) := by
  have hs : 0 < (spacing i : Real) := by exact_mod_cast hspacing i
  have hratio :
      (B.side i : Real) / (spacing i : Real) <=
        (Nat.ceil ((B.side i : Real) / (spacing i : Real)) : Real) :=
    Nat.le_ceil _
  have hbase :
      (B.side i : Real) <=
        (Nat.ceil ((B.side i : Real) / (spacing i : Real)) : Real) *
          (spacing i : Real) :=
    (div_le_iff₀ hs).mp hratio
  simp only [ceilHitBudget, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Floor/ceiling-shaped dense-grid count with no counting hypothesis. -/
theorem boxPointHitCount_le_prod_ceilHitBudget
    (B : FrameBox) (spacing : Fin 3 -> NNReal)
    {siteCount : Fin 3 -> Nat} (hspacing : forall i, 0 < spacing i)
    (x : Space) :
    boxPointHitCount B spacing (siteCount := siteCount) x <=
      ∏ i, ceilHitBudget B spacing i := by
  exact boxPointHitCount_le_prod_hitBudget B spacing
    (ceilHitBudget_pos B spacing)
    (side_lt_ceilHitBudget_mul_spacing B spacing hspacing) x

#print axioms nat_eq_of_mod_eq_of_abs_cast_sub_mul_le
#print axioms abs_inner_sub_inner_le_side
#print axioms boxLatticeSites_eq_of_residue_eq_of_add_mem_carrier
#print axioms boxPointHitCount_le_prod_hitBudget
#print axioms side_lt_ceilHitBudget_mul_spacing
#print axioms boxPointHitCount_le_prod_ceilHitBudget

end

end FamilyStickyDenseLatticeBoxPointCountV1
