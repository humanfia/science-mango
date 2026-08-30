import ArchonPhysics.BHOStretchedExponentialSummability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Annealed EFC bounds imply almost-sure BHO localization windows

This file isolates the probability-theoretic content of Lemma 3 in the
Bernardin--Huveneers--Olla localization argument.  Its sole model-specific
input is the displayed finite-volume annealed eigenfunction-correlator
expectation inequality.  Markov's inequality, a finite union bound,
summability, and the first Borel--Cantelli lemma are proved here.

In particular, this file does **not** assert that the random-mass operator
satisfies the EFC inequality.
-/

namespace ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli

open Filter MeasureTheory
open ArchonPhysics.BHORandomMassLocalizationSchedule
open ArchonPhysics.BHOStretchedExponentialSummability

noncomputable section

/-- The coordinate accuracy used outside the localization interval. -/
def bhoCoordinateThreshold (gamma : Real) (N : Nat) : Real :=
  (N : Real) ^ (-1 / gamma)

/-- The product threshold detected by an EFC when a normalized mode has one
large coordinate and a second coordinate violates the desired tail bound. -/
def bhoPairDetectionThreshold (gamma : Real) (N : Nat) : Real :=
  (N : Real) ^ (-(1 / 2 : Real)) * bhoCoordinateThreshold gamma N

/-- Two sites are separated beyond one BHO localization radius. -/
def IsBHOWindowSeparated
    (gamma : Real) {N : Nat} (x y : Fin N) : Prop :=
  bhoWindowScale gamma N < |(x.val : Real) - (y.val : Real)|

/-- The finite-volume hard-band eigenfunction correlator. -/
def hardEigenfunctionCorrelator
    {Omega : Type*}
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2)) : ENNReal := by
  classical
  exact ∑ q : Fin (n + 2),
    if hard n omega q then
      ENNReal.ofReal |coordinate n omega q x * coordinate n omega q y|
    else 0

/-- A separated pair is bad when its EFC reaches the product threshold. -/
def bhoEFCPairBadEvent
    {Omega : Type*}
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    (gamma : Real) (n : Nat) (x y : Fin (n + 2)) : Set Omega := by
  classical
  exact if IsBHOWindowSeparated gamma x y then
    {omega | ENNReal.ofReal (bhoPairDetectionThreshold gamma (n + 2)) <=
      hardEigenfunctionCorrelator hard coordinate n omega x y}
  else ∅

/-- The finite-volume bad event is the union over all ordered site pairs. -/
def bhoEFCBadEvent
    {Omega : Type*}
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    (gamma : Real) (n : Nat) : Set Omega :=
  ⋃ x : Fin (n + 2), ⋃ y : Fin (n + 2),
    bhoEFCPairBadEvent hard coordinate gamma n x y

/-- A concrete centered interval of radius `N^gamma`. -/
def bhoLocalizationInterval
    (gamma : Real) {N : Nat} (center : Fin N) : Set (Fin N) :=
  {x | |(x.val : Real) - (center.val : Real)| <= bhoWindowScale gamma N}

/-- Every hard mode has a width-`2 N^gamma` interval and coordinates at most
`N^(-1/gamma)` outside it. -/
def HasBHOLocalizationWindows
    {Omega : Type*}
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    (gamma : Real) (n : Nat) (omega : Omega) : Prop :=
  ∀ q : Fin (n + 2), hard n omega q ->
    ∃ center : Fin (n + 2),
      (∀ x ∈ bhoLocalizationInterval gamma center,
        ∀ y ∈ bhoLocalizationInterval gamma center,
          |(x.val : Real) - (y.val : Real)| <=
            2 * bhoWindowScale gamma (n + 2)) ∧
      ∀ y ∉ bhoLocalizationInterval gamma center,
        |coordinate n omega q y| <= bhoCoordinateThreshold gamma (n + 2)

/-- A normalized real vector has a coordinate of size at least `N^(-1/2)`.
This is the deterministic pigeonhole step in the EFC argument. -/
theorem exists_abs_ge_volume_rpow_neg_half
    {N : Nat} [NeZero N] (v : Fin N -> Real)
    (hnorm : ∑ i, |v i| ^ 2 = 1) :
    ∃ i, (N : Real) ^ (-(1 / 2 : Real)) <= |v i| := by
  by_contra h
  push_neg at h
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hsquare : ((N : Real) ^ (-(1 / 2 : Real))) ^ 2 = (N : Real)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hN.le]
    convert Real.rpow_neg_one (N : Real) using 1 <;> ring
  have hsum : ∑ i : Fin N, |v i| ^ 2 <
      ∑ _i : Fin N, ((N : Real) ^ (-(1 / 2 : Real))) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i _hi
      exact (sq_lt_sq₀ (abs_nonneg (v i))
        (Real.rpow_nonneg hN.le _)).2 (h i)
  rw [hnorm] at hsum
  have hright : ∑ _i : Fin N,
      ((N : Real) ^ (-(1 / 2 : Real))) ^ 2 = 1 := by
    rw [hsquare]
    simp [hN.ne']
  rw [hright] at hsum
  exact (lt_irrefl 1 hsum)

/-- The centered radius-`N^gamma` set has diameter at most `2 N^gamma`.
This is the exact interval-width assertion used in the localization output. -/
theorem bhoLocalizationInterval_diameter_le
    {gamma : Real} {N : Nat} {center x y : Fin N}
    (hx : x ∈ bhoLocalizationInterval gamma center)
    (hy : y ∈ bhoLocalizationInterval gamma center) :
    |(x.val : Real) - (y.val : Real)| <=
      2 * bhoWindowScale gamma N := by
  change |(x.val : Real) - (center.val : Real)| <=
    bhoWindowScale gamma N at hx
  change |(y.val : Real) - (center.val : Real)| <=
    bhoWindowScale gamma N at hy
  calc
    |(x.val : Real) - (y.val : Real)| =
        |((x.val : Real) - (center.val : Real)) -
          ((y.val : Real) - (center.val : Real))| := by congr 1 <;> ring
    _ <= |(x.val : Real) - (center.val : Real)| +
        |(y.val : Real) - (center.val : Real)| := abs_sub _ _
    _ <= bhoWindowScale gamma N + bhoWindowScale gamma N :=
      add_le_add hx hy
    _ = 2 * bhoWindowScale gamma N := by ring

/-- Outside the finite-volume EFC bad event, normalized hard modes have the
claimed BHO localization windows.  No probability input is used here. -/
theorem hasBHOLocalizationWindows_of_not_mem_badEvent
    {Omega : Type*}
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    {gamma : Real} (hgamma : 0 < gamma)
    (hnormalized : ∀ n omega q,
      ∑ x, |coordinate n omega q x| ^ 2 = 1)
    {n : Nat} {omega : Omega}
    (hgood : omega ∉ bhoEFCBadEvent hard coordinate gamma n) :
    HasBHOLocalizationWindows hard coordinate gamma n omega := by
  classical
  intro q hq
  let N : Nat := n + 2
  have hN : 0 < (N : Real) := by
    dsimp only [N]
    positivity
  have hcenterThreshold : 0 < (N : Real) ^ (-(1 / 2 : Real)) :=
    Real.rpow_pos_of_pos hN _
  have hcoordinateThreshold : 0 < bhoCoordinateThreshold gamma N := by
    exact Real.rpow_pos_of_pos hN _
  obtain ⟨center, hcenter⟩ :=
    exists_abs_ge_volume_rpow_neg_half
      (fun x => coordinate n omega q x) (hnormalized n omega q)
  refine ⟨center, ?_, ?_⟩
  · intro x hx y hy
    exact bhoLocalizationInterval_diameter_le hx hy
  · intro y hy
    by_contra htail
    have htail' : bhoCoordinateThreshold gamma N <
        |coordinate n omega q y| := lt_of_not_ge htail
    have hseparated : IsBHOWindowSeparated gamma center y := by
      change bhoWindowScale gamma N <
        |(center.val : Real) - (y.val : Real)|
      change ¬ |(y.val : Real) - (center.val : Real)| <=
        bhoWindowScale gamma N at hy
      rw [not_le] at hy
      simpa only [abs_sub_comm] using hy
    have hproduct : bhoPairDetectionThreshold gamma N <
        |coordinate n omega q center * coordinate n omega q y| := by
      rw [abs_mul]
      change (N : Real) ^ (-(1 / 2 : Real)) *
          bhoCoordinateThreshold gamma N <
        |coordinate n omega q center| * |coordinate n omega q y|
      exact (mul_lt_mul_of_pos_left htail' hcenterThreshold).trans_le
        (mul_le_mul_of_nonneg_right hcenter (abs_nonneg _))
    have hmodeTerm :
        ENNReal.ofReal
            |coordinate n omega q center * coordinate n omega q y| <=
          hardEigenfunctionCorrelator hard coordinate n omega center y := by
      change ENNReal.ofReal
          |coordinate n omega q center * coordinate n omega q y| <=
        ∑ r : Fin (n + 2),
          if hard n omega r then
            ENNReal.ofReal
              |coordinate n omega r center * coordinate n omega r y|
          else 0
      calc
        ENNReal.ofReal
            |coordinate n omega q center * coordinate n omega q y| =
            (if hard n omega q then
              ENNReal.ofReal
                |coordinate n omega q center * coordinate n omega q y|
            else 0) := by simp [hq]
        _ <= ∑ r : Fin (n + 2),
            if hard n omega r then
              ENNReal.ofReal
                |coordinate n omega r center * coordinate n omega r y|
            else 0 :=
          Finset.single_le_sum
            (f := fun r : Fin (n + 2) =>
              if hard n omega r then
                ENNReal.ofReal
                  |coordinate n omega r center * coordinate n omega r y|
              else 0) (fun _r _hr => bot_le) (Finset.mem_univ q)
    have hthreshold :
        ENNReal.ofReal (bhoPairDetectionThreshold gamma N) <=
          hardEigenfunctionCorrelator hard coordinate n omega center y :=
      (ENNReal.ofReal_le_ofReal hproduct.le).trans hmodeTerm
    have hpair : omega ∈
        bhoEFCPairBadEvent hard coordinate gamma n center y := by
      simp only [bhoEFCPairBadEvent, if_pos hseparated, Set.mem_setOf_eq]
      exact hthreshold
    apply hgood
    simp only [bhoEFCBadEvent, Set.mem_iUnion]
    exact ⟨center, y, hpair⟩

/-- The real Markov budget for one separated pair. -/
def bhoEFCPairProbabilityBudget
    (C alpha gamma decayRate : Real) (n : Nat) : Real :=
  C * bhoEFCWindowTail alpha gamma decayRate (n + 2) /
    bhoPairDetectionThreshold gamma (n + 2)

/-- The finite-volume union-bound budget, kept as the exact finite double
sum in `ENNReal`. -/
def bhoEFCBadProbabilityBudget
    (C alpha gamma decayRate : Real) (n : Nat) : ENNReal :=
  ∑ _x : Fin (n + 2), ∑ _y : Fin (n + 2),
    ENNReal.ofReal
      (bhoEFCPairProbabilityBudget C alpha gamma decayRate n)

/-- Markov's inequality and the finite union bound convert the displayed
annealed EFC inequality into a finite-volume bad-event probability bound. -/
theorem measure_bhoEFCBadEvent_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega)
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    {C alpha gamma decayRate : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hmeasurable : ∀ n x y,
      Measurable (fun omega =>
        hardEigenfunctionCorrelator hard coordinate n omega x y))
    (hEFC : ∀ n x y, IsBHOWindowSeparated gamma x y ->
      (∫⁻ omega,
        hardEigenfunctionCorrelator hard coordinate n omega x y ∂P) <=
        ENNReal.ofReal
          (C * bhoEFCWindowTail alpha gamma decayRate (n + 2)))
    (n : Nat) :
    P (bhoEFCBadEvent hard coordinate gamma n) <=
      bhoEFCBadProbabilityBudget C alpha gamma decayRate n := by
  classical
  let N : Nat := n + 2
  have hN : 0 < (N : Real) := by
    dsimp only [N]
    positivity
  have hthreshold :
      0 < bhoPairDetectionThreshold gamma N := by
    exact mul_pos (Real.rpow_pos_of_pos hN _)
      (Real.rpow_pos_of_pos hN _)
  have hpair : ∀ x y : Fin (n + 2),
      P (bhoEFCPairBadEvent hard coordinate gamma n x y) <=
        ENNReal.ofReal
          (bhoEFCPairProbabilityBudget C alpha gamma decayRate n) := by
    intro x y
    by_cases hseparated : IsBHOWindowSeparated gamma x y
    · rw [bhoEFCPairBadEvent, if_pos hseparated]
      calc
        P {omega |
            ENNReal.ofReal (bhoPairDetectionThreshold gamma (n + 2)) <=
              hardEigenfunctionCorrelator hard coordinate n omega x y} <=
            (∫⁻ omega,
              hardEigenfunctionCorrelator hard coordinate n omega x y ∂P) /
              ENNReal.ofReal
                (bhoPairDetectionThreshold gamma (n + 2)) :=
          meas_ge_le_lintegral_div
            (hmeasurable n x y).aemeasurable
            (ENNReal.ofReal_ne_zero_iff.mpr hthreshold)
            ENNReal.ofReal_ne_top
        _ <= ENNReal.ofReal
              (C * bhoEFCWindowTail alpha gamma decayRate (n + 2)) /
              ENNReal.ofReal
                (bhoPairDetectionThreshold gamma (n + 2)) := by
          gcongr
          exact hEFC n x y hseparated
        _ = ENNReal.ofReal
              (bhoEFCPairProbabilityBudget C alpha gamma decayRate n) := by
          rw [← ENNReal.ofReal_div_of_pos hthreshold]
          rfl
    · rw [bhoEFCPairBadEvent, if_neg hseparated, measure_empty]
      exact bot_le
  change P (⋃ x : Fin (n + 2), ⋃ y : Fin (n + 2),
      bhoEFCPairBadEvent hard coordinate gamma n x y) <=
    ∑ _x : Fin (n + 2), ∑ _y : Fin (n + 2),
      ENNReal.ofReal
        (bhoEFCPairProbabilityBudget C alpha gamma decayRate n)
  calc
    P (⋃ x : Fin (n + 2), ⋃ y : Fin (n + 2),
        bhoEFCPairBadEvent hard coordinate gamma n x y) <=
      ∑ x : Fin (n + 2),
        P (⋃ y : Fin (n + 2),
          bhoEFCPairBadEvent hard coordinate gamma n x y) :=
      measure_iUnion_fintype_le P _
    _ <= ∑ x : Fin (n + 2), ∑ y : Fin (n + 2),
        P (bhoEFCPairBadEvent hard coordinate gamma n x y) := by
      gcongr with x
      exact measure_iUnion_fintype_le P _
    _ <= ∑ _x : Fin (n + 2), ∑ _y : Fin (n + 2),
        ENNReal.ofReal
          (bhoEFCPairProbabilityBudget C alpha gamma decayRate n) := by
      gcongr with x y
      exact hpair x y

/-- The pair Markov loss is exactly the inverse normalization/coordinate
threshold, hence a polynomial factor. -/
theorem bhoEFCPairProbabilityBudget_eq
    {C alpha gamma decayRate : Real} (n : Nat) :
    bhoEFCPairProbabilityBudget C alpha gamma decayRate n =
      C * (((n + 2 : Nat) : Real)) ^ ((1 / 2 : Real) + 1 / gamma) *
        bhoEFCWindowTail alpha gamma decayRate (n + 2) := by
  have hN : 0 < (((n + 2 : Nat) : Real)) := by positivity
  have hpairThreshold :
      bhoPairDetectionThreshold gamma (n + 2) =
        (((n + 2 : Nat) : Real)) ^
          (-((1 / 2 : Real) + 1 / gamma)) := by
    rw [bhoPairDetectionThreshold, bhoCoordinateThreshold,
      ← Real.rpow_add hN]
    congr 1
    ring
  rw [bhoEFCPairProbabilityBudget, hpairThreshold, div_eq_mul_inv,
    Real.rpow_neg hN.le]
  simp only [inv_inv]
  ring

/-- The real version of the exact double-union probability budget. -/
def bhoEFCBadProbabilityBudgetReal
    (C alpha gamma decayRate : Real) (n : Nat) : Real :=
  (((n + 2 : Nat) : Real)) ^ 2 *
    bhoEFCPairProbabilityBudget C alpha gamma decayRate n

/-- For a nonnegative EFC constant, the `ENNReal` finite-union budget is the
`ofReal` image of its real counterpart. -/
theorem bhoEFCBadProbabilityBudget_eq_ofReal
    {C alpha gamma decayRate : Real} (hC : 0 <= C) (n : Nat) :
    bhoEFCBadProbabilityBudget C alpha gamma decayRate n =
      ENNReal.ofReal
        (bhoEFCBadProbabilityBudgetReal C alpha gamma decayRate n) := by
  have hpairNonneg :
      0 <= bhoEFCPairProbabilityBudget C alpha gamma decayRate n := by
    rw [bhoEFCPairProbabilityBudget_eq]
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      (Real.exp_nonneg _)
  rw [bhoEFCBadProbabilityBudget, bhoEFCBadProbabilityBudgetReal]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  calc
    ((n + 2 : Nat) : ENNReal) *
        (((n + 2 : Nat) : ENNReal) *
          ENNReal.ofReal
            (bhoEFCPairProbabilityBudget C alpha gamma decayRate n)) =
      ENNReal.ofReal (((n + 2 : Nat) : Real)) *
        (ENNReal.ofReal (((n + 2 : Nat) : Real)) *
          ENNReal.ofReal
            (bhoEFCPairProbabilityBudget C alpha gamma decayRate n)) := by
      norm_cast
    _ = ENNReal.ofReal
        ((((n + 2 : Nat) : Real)) *
          (((n + 2 : Nat) : Real) *
            bhoEFCPairProbabilityBudget C alpha gamma decayRate n)) := by
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = ENNReal.ofReal
        ((((n + 2 : Nat) : Real)) ^ 2 *
          bhoEFCPairProbabilityBudget C alpha gamma decayRate n) := by
      congr 1
      ring

/-- The two-site union loss adds exactly two polynomial powers; the resulting
real probability budget is still summable under the scale separation. -/
theorem summable_bhoEFCBadProbabilityBudgetReal
    {C alpha gamma decayRate : Real}
    (hscale : 2 * alpha < gamma) (hdecay : 0 < decayRate) :
    Summable
      (bhoEFCBadProbabilityBudgetReal C alpha gamma decayRate) := by
  have hbase :=
    summable_polynomial_mul_bhoEFCWindowTail
      (polynomialPower := (5 / 2 : Real) + 1 / gamma)
      hscale hdecay
  have hscaled := hbase.mul_left C
  apply hscaled.congr
  intro n
  rw [bhoEFCBadProbabilityBudgetReal,
    bhoEFCPairProbabilityBudget_eq]
  have hN : 0 < (((n + 2 : Nat) : Real)) := by positivity
  calc
    C * ((((n + 2 : Nat) : Real)) ^
          ((5 / 2 : Real) + 1 / gamma) *
        bhoEFCWindowTail alpha gamma decayRate (n + 2)) =
      C * ((((n + 2 : Nat) : Real)) ^
          ((5 / 2 : Real) + 1 / gamma)) *
        bhoEFCWindowTail alpha gamma decayRate (n + 2) := by ring
    _ = ((((n + 2 : Nat) : Real)) ^ 2) *
        (C * (((n + 2 : Nat) : Real)) ^
          ((1 / 2 : Real) + 1 / gamma) *
          bhoEFCWindowTail alpha gamma decayRate (n + 2)) := by
      have hpower :
          (((n + 2 : Nat) : Real)) ^
              ((5 / 2 : Real) + 1 / gamma) =
            ((((n + 2 : Nat) : Real)) ^ (2 : Real)) *
              (((n + 2 : Nat) : Real)) ^
                ((1 / 2 : Real) + 1 / gamma) := by
        calc
          _ = (((n + 2 : Nat) : Real)) ^
              ((2 : Real) + ((1 / 2 : Real) + 1 / gamma)) := by
                congr 1
                ring
          _ = (((n + 2 : Nat) : Real)) ^ (2 : Real) *
              (((n + 2 : Nat) : Real)) ^
                ((1 / 2 : Real) + 1 / gamma) :=
            Real.rpow_add hN _ _
      have htwo : (((n + 2 : Nat) : Real)) ^ (2 : Real) =
          (((n + 2 : Nat) : Real)) ^ (2 : Nat) :=
        Real.rpow_natCast _ 2
      rw [hpower, htwo]
      ring

/-- The finite-volume bad-event budgets have finite total mass. -/
theorem bhoEFCBadProbabilityBudget_tsum_ne_top
    {C alpha gamma decayRate : Real}
    (hC : 0 <= C) (hscale : 2 * alpha < gamma)
    (hdecay : 0 < decayRate) :
    (∑' n : Nat, bhoEFCBadProbabilityBudget
      C alpha gamma decayRate n) ≠ (⊤ : ENNReal) := by
  rw [show (fun n : Nat =>
      bhoEFCBadProbabilityBudget C alpha gamma decayRate n) =
      (fun n : Nat => ENNReal.ofReal
        (bhoEFCBadProbabilityBudgetReal C alpha gamma decayRate n)) by
    funext n
    exact bhoEFCBadProbabilityBudget_eq_ofReal hC n]
  exact (summable_bhoEFCBadProbabilityBudgetReal
    (C := C) hscale hdecay).tsum_ofReal_lt_top.ne

/-- The EFC inequality makes the actual finite-volume bad-event probabilities
summable. -/
theorem bhoEFCBadEvent_measure_tsum_ne_top
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega)
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    {C alpha gamma decayRate : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hscale : 2 * alpha < gamma) (hdecay : 0 < decayRate)
    (hmeasurable : ∀ n x y,
      Measurable (fun omega =>
        hardEigenfunctionCorrelator hard coordinate n omega x y))
    (hEFC : ∀ n x y, IsBHOWindowSeparated gamma x y ->
      (∫⁻ omega,
        hardEigenfunctionCorrelator hard coordinate n omega x y ∂P) <=
        ENNReal.ofReal
          (C * bhoEFCWindowTail alpha gamma decayRate (n + 2))) :
    (∑' n : Nat, P (bhoEFCBadEvent hard coordinate gamma n)) ≠
      (⊤ : ENNReal) := by
  have hsumLe :
      (∑' n : Nat, P (bhoEFCBadEvent hard coordinate gamma n)) <=
        ∑' n : Nat,
          bhoEFCBadProbabilityBudget C alpha gamma decayRate n :=
    ENNReal.tsum_le_tsum fun n =>
      measure_bhoEFCBadEvent_le P hard coordinate hC hgamma
        hmeasurable hEFC n
  exact (hsumLe.trans_lt
    (lt_top_iff_ne_top.mpr
      (bhoEFCBadProbabilityBudget_tsum_ne_top
        hC hscale hdecay))).ne

/-- Generic BHO Lemma 3 probability bridge: an explicit annealed
finite-volume EFC expectation inequality implies that almost surely, at all
sufficiently large volumes, every normalized hard mode admits a localization
interval of the stated width and has the stated coordinate tail. -/
theorem eventually_hasBHOLocalizationWindows_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega)
    (hard : (n : Nat) -> Omega -> Fin (n + 2) -> Prop)
    (coordinate : (n : Nat) -> Omega -> Fin (n + 2) -> Fin (n + 2) -> Real)
    {C alpha gamma decayRate : Real}
    (hC : 0 <= C) (hgamma : 0 < gamma)
    (hscale : 2 * alpha < gamma) (hdecay : 0 < decayRate)
    (hnormalized : ∀ n omega q,
      ∑ x, |coordinate n omega q x| ^ 2 = 1)
    (hmeasurable : ∀ n x y,
      Measurable (fun omega =>
        hardEigenfunctionCorrelator hard coordinate n omega x y))
    (hEFC : ∀ n x y, IsBHOWindowSeparated gamma x y ->
      (∫⁻ omega,
        hardEigenfunctionCorrelator hard coordinate n omega x y ∂P) <=
        ENNReal.ofReal
          (C * bhoEFCWindowTail alpha gamma decayRate (n + 2))) :
    ∀ᵐ omega ∂P, ∀ᶠ n : Nat in atTop,
      HasBHOLocalizationWindows hard coordinate gamma n omega := by
  have hbc := ae_eventually_notMem
    (bhoEFCBadEvent_measure_tsum_ne_top P hard coordinate
      hC hgamma hscale hdecay hmeasurable hEFC)
  filter_upwards [hbc] with omega homega
  filter_upwards [homega] with n hn
  exact hasBHOLocalizationWindows_of_not_mem_badEvent
    hard coordinate hgamma hnormalized hn

end

end ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli
