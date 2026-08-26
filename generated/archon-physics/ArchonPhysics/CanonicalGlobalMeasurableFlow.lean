import ArchonPhysics.CoerciveHamiltonianGlobalExistence
import ArchonPhysics.MeasurableHamiltonianDynamics

/-!
# Canonical measurable global flows for compactly supported vector fields

Global existence alone gives only a pointwise existential trajectory.  For a
globally Lipschitz field, uniqueness turns a classical choice of those curves
into a canonical solution map.  Gronwall's estimate makes every fixed-time
solution map continuous, and continuous sample paths then give joint
measurability in initial point and time.

The final part specializes this construction to the smooth norm cutoff used
for coercive Hamiltonian continuation.  Agreement with the untruncated field
is stated under the exact radius condition; invariance of a particular energy
shell is deliberately left to the model-specific layer.
-/

namespace ArchonPhysics.CanonicalGlobalMeasurableFlow

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianGlobalExistence

noncomputable section

/-- Choose the unique global integral curve.  The choice is canonical at the
mathematical level because global Lipschitz uniqueness is proved below. -/
def canonicalGlobalCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (x : E) : Real → E :=
  Classical.choose (hglobal x)

theorem canonicalGlobalCurve_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (x : E) :
    canonicalGlobalCurve hglobal x 0 = x :=
  (Classical.choose_spec (hglobal x)).1

theorem canonicalGlobalCurve_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (x : E) (t : Real) :
    HasDerivAt (canonicalGlobalCurve hglobal x)
      (f (canonicalGlobalCurve hglobal x t)) t :=
  (Classical.choose_spec (hglobal x)).2 t

/-- Global Lipschitz uniqueness removes all dependence on which existential
trajectory witness was supplied. -/
theorem canonicalGlobalCurve_eq_of_global_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E} {K : NNReal}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (hlip : LipschitzWith K f) (x : E)
    (gamma : Real → E) (hgamma0 : gamma 0 = x)
    (hgamma : ∀ t, HasDerivAt gamma (f (gamma t)) t) :
    canonicalGlobalCurve hglobal x = gamma := by
  apply ODE_solution_unique_univ
    (v := fun _ : Real => f) (s := fun _ => Set.univ)
    (K := K) (t₀ := 0)
  · exact fun _ => hlip.lipschitzOnWith
  · exact fun t => ⟨canonicalGlobalCurve_hasDerivAt hglobal x t,
      Set.mem_univ _⟩
  · exact fun t => ⟨hgamma t, Set.mem_univ _⟩
  · rw [canonicalGlobalCurve_zero hglobal x, hgamma0]

/-- At every fixed time, the canonical solution map is Lipschitz.  The
constant `exp(K |t|)` is the two-sided Gronwall bound. -/
theorem canonicalGlobalCurve_lipschitz_fixedTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E} {K : NNReal}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (hlip : LipschitzWith K f) (t : Real) :
    LipschitzWith
      ⟨Real.exp ((K : Real) * |t|), (Real.exp_pos _).le⟩
      (fun x : E => canonicalGlobalCurve hglobal x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (canonicalGlobalCurve hglobal x t)
    (canonicalGlobalCurve hglobal y t) ≤
      Real.exp ((K : Real) * |t|) * dist x y
  by_cases ht : 0 ≤ t
  · have hxContinuous : ContinuousOn
        (canonicalGlobalCurve hglobal x) (Set.Icc 0 t) :=
      HasDerivAt.continuousOn fun s _hs =>
        canonicalGlobalCurve_hasDerivAt hglobal x s
    have hyContinuous : ContinuousOn
        (canonicalGlobalCurve hglobal y) (Set.Icc 0 t) :=
      HasDerivAt.continuousOn fun s _hs =>
        canonicalGlobalCurve_hasDerivAt hglobal y s
    have hbound := dist_le_of_trajectories_ODE
      (v := fun _ : Real => f) (K := K) (a := 0) (b := t)
      (fun _ => hlip) hxContinuous
      (fun s _hs =>
        (canonicalGlobalCurve_hasDerivAt hglobal x s).hasDerivWithinAt)
      hyContinuous
      (fun s _hs =>
        (canonicalGlobalCurve_hasDerivAt hglobal y s).hasDerivWithinAt)
      (show dist (canonicalGlobalCurve hglobal x 0)
        (canonicalGlobalCurve hglobal y 0) ≤ dist x y by
          simp [canonicalGlobalCurve_zero hglobal])
      t ⟨ht, le_rfl⟩
    calc
      dist (canonicalGlobalCurve hglobal x t)
          (canonicalGlobalCurve hglobal y t) ≤
          dist x y * Real.exp ((K : Real) * (t - 0)) := hbound
      _ = Real.exp ((K : Real) * |t|) * dist x y := by
        rw [abs_of_nonneg ht]
        ring_nf
  · have ht' : t ≤ 0 := le_of_not_ge ht
    let reverseX : Real → E :=
      fun s => canonicalGlobalCurve hglobal x (-s)
    let reverseY : Real → E :=
      fun s => canonicalGlobalCurve hglobal y (-s)
    have hreverseX : ∀ s, HasDerivAt reverseX
        (-f (reverseX s)) s := by
      intro s
      change HasDerivAt
        (canonicalGlobalCurve hglobal x ∘ fun r : Real => -r)
        (-f (canonicalGlobalCurve hglobal x (-s))) s
      simpa only [Function.comp_apply, neg_smul, one_smul] using
        (canonicalGlobalCurve_hasDerivAt hglobal x (-s)).scomp s
          (hasDerivAt_neg s)
    have hreverseY : ∀ s, HasDerivAt reverseY
        (-f (reverseY s)) s := by
      intro s
      change HasDerivAt
        (canonicalGlobalCurve hglobal y ∘ fun r : Real => -r)
        (-f (canonicalGlobalCurve hglobal y (-s))) s
      simpa only [Function.comp_apply, neg_smul, one_smul] using
        (canonicalGlobalCurve_hasDerivAt hglobal y (-s)).scomp s
          (hasDerivAt_neg s)
    have hxContinuous : ContinuousOn reverseX (Set.Icc 0 (-t)) :=
      HasDerivAt.continuousOn fun s _hs => hreverseX s
    have hyContinuous : ContinuousOn reverseY (Set.Icc 0 (-t)) :=
      HasDerivAt.continuousOn fun s _hs => hreverseY s
    have hbound := dist_le_of_trajectories_ODE
      (v := fun _ : Real => fun z => -f z) (K := K)
      (a := 0) (b := -t) (fun _ => hlip.neg)
      hxContinuous (fun s _hs => (hreverseX s).hasDerivWithinAt)
      hyContinuous (fun s _hs => (hreverseY s).hasDerivWithinAt)
      (show dist (reverseX 0) (reverseY 0) ≤ dist x y by
        simp [reverseX, reverseY, canonicalGlobalCurve_zero hglobal])
      (-t) ⟨neg_nonneg.mpr ht', le_rfl⟩
    calc
      dist (canonicalGlobalCurve hglobal x t)
          (canonicalGlobalCurve hglobal y t) =
          dist (reverseX (-t)) (reverseY (-t)) := by
            simp [reverseX, reverseY]
      _ ≤ dist x y * Real.exp ((K : Real) * ((-t) - 0)) := hbound
      _ = Real.exp ((K : Real) * |t|) * dist x y := by
        rw [abs_of_nonpos ht']
        ring_nf

theorem continuous_canonicalGlobalCurve_fixedTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E} {K : NNReal}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (hlip : LipschitzWith K f) (t : Real) :
    Continuous (fun x : E => canonicalGlobalCurve hglobal x t) :=
  (canonicalGlobalCurve_lipschitz_fixedTime hglobal hlip t).continuous

theorem continuous_canonicalGlobalCurve_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : E → E}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (x : E) : Continuous (canonicalGlobalCurve hglobal x) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (canonicalGlobalCurve_hasDerivAt hglobal x t).continuousAt

/-- Fixed-time continuity plus continuous paths yields the desired joint
initial-data/time measurability. -/
theorem measurable_canonicalGlobalCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal}
    (hglobal : ∀ x : E, ∃ gamma : Real → E, gamma 0 = x ∧
      ∀ t : Real, HasDerivAt gamma (f (gamma t)) t)
    (hlip : LipschitzWith K f) :
    Measurable fun p : E × Real =>
      canonicalGlobalCurve hglobal p.1 p.2 := by
  exact MeasurableHamiltonianDynamics.measurable_joint_trajectory_of_continuous_paths
    (fun x t => canonicalGlobalCurve hglobal x t)
    (continuous_canonicalGlobalCurve_path hglobal)
    (fun t => (continuous_canonicalGlobalCurve_fixedTime hglobal hlip t).measurable)

/-- The globally measurable canonical flow of a compactly supported `C¹`
vector field. -/
def canonicalCompactSupportFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (hcompact : HasCompactSupport f) : E × Real → E :=
  fun p => canonicalGlobalCurve
    (fun x => exists_global_integralCurve_of_contDiff_hasCompactSupport
      hf hcompact x) p.1 p.2

theorem canonicalCompactSupportFlow_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (hcompact : HasCompactSupport f) :
    Measurable (canonicalCompactSupportFlow hf hcompact) := by
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hcompact hf one_ne_zero
  exact measurable_canonicalGlobalCurve
    (fun x => exists_global_integralCurve_of_contDiff_hasCompactSupport
      hf hcompact x) hK

theorem canonicalCompactSupportFlow_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (hcompact : HasCompactSupport f) (x : E) :
    canonicalCompactSupportFlow hf hcompact (x, 0) = x :=
  canonicalGlobalCurve_zero
    (fun y => exists_global_integralCurve_of_contDiff_hasCompactSupport
      hf hcompact y) x

theorem canonicalCompactSupportFlow_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [ContinuousSMul Real E] [FiniteDimensional Real E]
    {f : E → E} (hf : ContDiff Real 1 f)
    (hcompact : HasCompactSupport f) (x : E) (t : Real) :
    HasDerivAt (fun s => canonicalCompactSupportFlow hf hcompact (x, s))
      (f (canonicalCompactSupportFlow hf hcompact (x, t))) t :=
  canonicalGlobalCurve_hasDerivAt
    (fun y => exists_global_integralCurve_of_contDiff_hasCompactSupport
      hf hcompact y) x t

/-- Canonical global flow for the smooth norm cutoff of an arbitrary `C¹`
field. -/
def canonicalCutoffFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R) :
    E × Real → E :=
  canonicalCompactSupportFlow
    (normCutoffVectorField_contDiff hf R hR)
    (normCutoffVectorField_hasCompactSupport f R hR)

theorem canonicalCutoffFlow_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R) :
    Measurable (canonicalCutoffFlow f hf R hR) :=
  canonicalCompactSupportFlow_measurable
    (normCutoffVectorField_contDiff hf R hR)
    (normCutoffVectorField_hasCompactSupport f R hR)

theorem canonicalCutoffFlow_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R)
    (x : E) : canonicalCutoffFlow f hf R hR (x, 0) = x :=
  canonicalCompactSupportFlow_zero
    (normCutoffVectorField_contDiff hf R hR)
    (normCutoffVectorField_hasCompactSupport f R hR) x

theorem canonicalCutoffFlow_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R)
    (x : E) (t : Real) :
    HasDerivAt (fun s => canonicalCutoffFlow f hf R hR (x, s))
      (normCutoffVectorField f R hR
        (canonicalCutoffFlow f hf R hR (x, t))) t :=
  canonicalCompactSupportFlow_hasDerivAt
    (normCutoffVectorField_contDiff hf R hR)
    (normCutoffVectorField_hasCompactSupport f R hR) x t

/-- Inside the cutoff radius, the canonical cutoff flow solves the original
ODE exactly. -/
theorem canonicalCutoffFlow_hasDerivAt_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R)
    (x : E) (t : Real)
    (hinside : ‖canonicalCutoffFlow f hf R hR (x, t)‖ ≤ R) :
    HasDerivAt (fun s => canonicalCutoffFlow f hf R hR (x, s))
      (f (canonicalCutoffFlow f hf R hR (x, t))) t := by
  have hderiv := canonicalCutoffFlow_hasDerivAt f hf R hR x t
  rw [normCutoffVectorField_eq_of_norm_le f R hR hinside] at hderiv
  exact hderiv

/-- If an original global solution stays inside the cutoff radius, uniqueness
identifies it with the canonical cutoff flow.  This is the exact continuation
bridge needed by a model-specific invariant energy shell. -/
theorem canonicalCutoffFlow_eq_of_global_solution_inside
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : E → E) (hf : ContDiff Real 1 f) (R : Real) (hR : 0 ≤ R)
    (x : E) (gamma : Real → E) (hgamma0 : gamma 0 = x)
    (hgamma : ∀ t, HasDerivAt gamma (f (gamma t)) t)
    (hinside : ∀ t, ‖gamma t‖ ≤ R) :
    (fun t => canonicalCutoffFlow f hf R hR (x, t)) = gamma := by
  let truncated : E → E := normCutoffVectorField f R hR
  have htruncatedContDiff : ContDiff Real 1 truncated :=
    normCutoffVectorField_contDiff hf R hR
  have htruncatedCompact : HasCompactSupport truncated :=
    normCutoffVectorField_hasCompactSupport f R hR
  have hgammaTruncated : ∀ t,
      HasDerivAt gamma (truncated (gamma t)) t := by
    intro t
    change HasDerivAt gamma
      (normCutoffVectorField f R hR (gamma t)) t
    rw [normCutoffVectorField_eq_of_norm_le f R hR (hinside t)]
    exact hgamma t
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    htruncatedCompact htruncatedContDiff one_ne_zero
  have heq := canonicalGlobalCurve_eq_of_global_solution
    (fun y => exists_global_integralCurve_of_contDiff_hasCompactSupport
      htruncatedContDiff htruncatedCompact y) hK x gamma hgamma0
      hgammaTruncated
  simpa only [canonicalCutoffFlow, canonicalCompactSupportFlow, truncated] using heq

end

end ArchonPhysics.CanonicalGlobalMeasurableFlow
