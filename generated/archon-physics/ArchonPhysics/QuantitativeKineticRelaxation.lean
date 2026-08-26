import Mathlib
import ArchonPhysics.KineticRescaling
import ArchonPhysics.WaveKineticEquation

/-!
# Conditional kinetic uniqueness, rescaling, and robust crossing contracts

This module connects the parameterized wave kinetic predicate to the generic
effective-equation rescaling API already present in `ArchonPhysics`.  It also
records the minimum explicit contracts needed by later quantitative-relaxation
work.

The contracts below are hypotheses.  No theorem in this file asserts that the
collision operator of the target random lattice satisfies uniqueness,
well-posedness, entropy dissipation, nondegeneracy, or a robust crossing law.
-/

namespace ArchonPhysics

noncomputable section

/-- Global uniqueness for supplied solutions of every coupled kinetic IVP. -/
def UniqueWaveKineticSolutions {ι : Type} [Fintype ι]
    (data : CollisionData ι) : Prop :=
  ∀ (g : Real) (initial : KineticState ι) (D E : Real → KineticState ι),
    SolvesWaveKineticEquation data g initial D →
      SolvesWaveKineticEquation data g initial E → D = E

/--
The minimal admissibility contract used for exact time rescaling in this
module.  It contains only a uniqueness hypothesis; the name does not assert
that an exact microscopic collision kernel has been identified or admitted.
-/
structure AdmissibleKineticKernel {ι : Type} [Fintype ι]
    (data : CollisionData ι) : Prop where
  /-- Uniqueness of any two supplied trajectories with the same IVP data. -/
  uniqueSolutions : UniqueWaveKineticSolutions data

/--
The wave-kinetic predicate is definitionally the existing generic effective
kinetic predicate instantiated with the supplied collision map.
-/
theorem solvesWaveKineticEquation_iff_kineticRescaling {ι : Type} [Fintype ι]
    (data : CollisionData ι) (g : Real) (initial : KineticState ι)
    (D : Real → KineticState ι) :
    SolvesWaveKineticEquation data g initial D ↔
      KineticRescaling.SolvesKineticEquation
        data.collision g initial D := by
  rfl

/--
Explicit uniqueness transports the unit-coupling trajectory by `t ↦ g^2 t`.

Both trajectories and their uniqueness are hypotheses; this theorem does not
construct a solution or establish admissibility of a physical collision
kernel.
-/
theorem waveKineticSolution_rescale {ι : Type} [Fintype ι]
    (data : CollisionData ι) (g : Real) (initial : KineticState ι)
    (D1 Dg : Real → KineticState ι)
    (hD1 : SolvesWaveKineticEquation data 1 initial D1)
    (hDg : SolvesWaveKineticEquation data g initial Dg)
    (hunique : ∀ D E : Real → KineticState ι,
      SolvesWaveKineticEquation data g initial D →
        SolvesWaveKineticEquation data g initial E → D = E) :
    Dg = fun t => D1 (g ^ 2 * t) := by
  apply KineticRescaling.kineticSolution_rescale
    data.collision g initial D1 Dg
  · exact
      (solvesWaveKineticEquation_iff_kineticRescaling
        data 1 initial D1).mp hD1
  · exact
      (solvesWaveKineticEquation_iff_kineticRescaling
        data g initial Dg).mp hDg
  · intro D E hD hE
    apply hunique D E
    · exact
        (solvesWaveKineticEquation_iff_kineticRescaling
          data g initial D).mpr hD
    · exact
        (solvesWaveKineticEquation_iff_kineticRescaling
          data g initial E).mpr hE

/-- The named uniqueness contract supplies the preceding rescaling theorem. -/
theorem waveKineticSolution_rescale_of_admissible {ι : Type} [Fintype ι]
    (data : CollisionData ι) (hadmissible : AdmissibleKineticKernel data)
    (g : Real) (initial : KineticState ι)
    (D1 Dg : Real → KineticState ι)
    (hD1 : SolvesWaveKineticEquation data 1 initial D1)
    (hDg : SolvesWaveKineticEquation data g initial Dg) :
    Dg = fun t => D1 (g ^ 2 * t) := by
  apply waveKineticSolution_rescale data g initial D1 Dg hD1 hDg
  exact hadmissible.uniqueSolutions g initial

/-- The late-window kinetic equipartition distance as a function of window endpoint. -/
def kineticEquipartitionProfile {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu : Real) : Real → Real :=
  fun T => kineticEquipartitionDistance data D mu T

/--
A robust first crossing of a real-valued distance below `delta`.

`beforeMargin` supplies a uniform positive margin on every compact interval
ending a positive distance before the crossing time.  `afterMargin` supplies,
in every positive right-hand window, a point that is below the threshold by a
positive margin.  This pointwise right-hand condition is compatible with a
continuous distance satisfying `distance tauStar = delta`; it deliberately
does not demand one uniform margin all the way down to `tauStar`.  Existence of
this structure is never asserted unconditionally.
-/
structure RobustKineticFirstCrossing (distance : Real → Real)
    (delta tauStar : Real) : Prop where
  /-- The proposed first-crossing scale is positive. -/
  tauStar_pos : 0 < tauStar
  /-- Uniform separation above the threshold away from the crossing time. -/
  beforeMargin :
    ∀ ε, 0 < ε → ε < tauStar →
      ∃ margin, 0 < margin ∧
        ∀ t, 0 < t → t ≤ tauStar - ε →
          delta + margin ≤ distance t
  /-- Every right-hand window contains a point robustly below the threshold. -/
  afterMargin :
    ∀ ε, 0 < ε →
      ∃ t margin, tauStar < t ∧ t < tauStar + ε ∧
        0 < margin ∧ distance t ≤ delta - margin

/-- Before a robust crossing, the distance is strictly above the threshold. -/
theorem RobustKineticFirstCrossing.distance_gt_before
    {distance : Real → Real} {delta tauStar ε t : Real}
    (hcross : RobustKineticFirstCrossing distance delta tauStar)
    (hε_pos : 0 < ε) (hε_lt : ε < tauStar)
    (ht_pos : 0 < t) (ht_le : t ≤ tauStar - ε) :
    delta < distance t := by
  obtain ⟨margin, hmargin_pos, hbound⟩ :=
    hcross.beforeMargin ε hε_pos hε_lt
  have h := hbound t ht_pos ht_le
  linarith

/-- Every positive right-hand window contains a strictly-below-threshold time. -/
theorem RobustKineticFirstCrossing.exists_strict_hit_in_right_window
    {distance : Real → Real} {delta tauStar ε : Real}
    (hcross : RobustKineticFirstCrossing distance delta tauStar)
    (hε_pos : 0 < ε) :
    ∃ t, tauStar < t ∧ t < tauStar + ε ∧ distance t < delta := by
  obtain ⟨t, margin, ht_after, ht_before, hmargin_pos, hbound⟩ :=
    hcross.afterMargin ε hε_pos
  exact ⟨t, ht_after, ht_before, by linarith⟩

/-- A robust crossing supplies an explicit strictly-below-threshold time. -/
theorem RobustKineticFirstCrossing.exists_strict_hit_after
    {distance : Real → Real} {delta tauStar : Real}
    (hcross : RobustKineticFirstCrossing distance delta tauStar) :
    ∃ t, tauStar < t ∧ distance t < delta := by
  obtain ⟨t, ht_after, _, ht⟩ :=
    hcross.exists_strict_hit_in_right_window (by norm_num : (0 : Real) < 1)
  exact ⟨t, ht_after, ht⟩

/-- The robust-crossing contract specialized to the modal-energy observable. -/
def RobustKineticEquipartitionCrossing {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu delta tauStar : Real) : Prop :=
  RobustKineticFirstCrossing
    (kineticEquipartitionProfile data D mu) delta tauStar

/-- The kinetic crossing adapter is transparent and adds no occurrence claim. -/
theorem robustKineticEquipartitionCrossing_iff
    {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu delta tauStar : Real) :
    RobustKineticEquipartitionCrossing data D mu delta tauStar ↔
      RobustKineticFirstCrossing
        (fun T => kineticEquipartitionDistance data D mu T)
        delta tauStar := by
  rfl

end

end ArchonPhysics
