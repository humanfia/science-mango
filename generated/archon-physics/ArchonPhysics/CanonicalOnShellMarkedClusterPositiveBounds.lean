import ArchonPhysics.CanonicalOnShellMarkedClusterExistence
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.Cofinite
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Positive canonical on-shell clusters from two-sided broadened-mass bounds

A positive convergent scalar broadened mass is more than compactness needs.
It is enough that, along a time sequence tending to infinity, the actual
unnormalized scalar broadened masses are eventually bounded above and bounded
away from zero.  The common compact marked support then gives a convergent
subsequence, and continuity of total mass preserves both bounds in the limit.

This criterion does not assume a density and does not assert the required
model-specific bounds.  For the canonical iid random-mass model, proving those
bounds remains the analytic small-ball/on-shell trace problem.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellMarkedClusterPositiveBounds

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterExistence
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Eventual positive lower and finite upper bounds on the actual scalar
broadened collision mass produce a nonzero on-shell marked cluster.  Unlike
the earlier convergence criterion, no scalar mass limit is supplied: the
proof selects one together with the marked weakly convergent subsequence. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_eventual_scalarMass_bounds
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (massLower massUpper : NNReal) (hmassLower : 0 < massLower)
    (hmassBounds : ∀ᶠ n in atTop,
      massLower <=
          (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time n) (htime_pos n)).mass /\
        (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time n) (htime_pos n)).mass <=
          massUpper) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble decayInteractionSign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          massLower <= collision.collisionMeasure.mass /\
          collision.collisionMeasure.mass <= massUpper /\
          collision.collisionMeasure ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmassBounds
  let mu : Nat -> FiniteMeasure (Fin 3 -> RankFrequencyMark) := fun j =>
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      ensemble decayInteractionSign (time (N + j)) (htime_pos (N + j))
  have hmassEq : forall n,
      (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n)).mass =
        (canonicalBroadenedCollisionPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n)).mass := by
    intro n
    apply NNReal.eq
    exact canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
      ensemble decayInteractionSign (time n) (htime_pos n)
  let markedMass : Nat -> NNReal := fun j => (mu j).mass
  have hmarkedBounds : forall j,
      markedMass j ∈ Set.Icc massLower massUpper := by
    intro j
    rw [show markedMass j =
        (canonicalBroadenedCollisionPerSiteMeasureLimit
          ensemble decayInteractionSign (time (N + j))
            (htime_pos (N + j))).mass by
      simpa [markedMass, mu] using hmassEq (N + j)]
    exact hN (N + j) (Nat.le_add_right N j)
  obtain ⟨massLimit, hmassLimitBounds, massSubsequence,
      hmassSubsequence, hmassTendsto⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc massLower massUpper)).tendsto_subseq
      hmarkedBounds
  have hmassLimitPos : 0 < massLimit :=
    hmassLower.trans_le hmassLimitBounds.1
  have hsupport : forall j,
      (mu (massSubsequence j) : Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
    intro j
    dsimp only [mu]
    exact
      canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
        ensemble decayInteractionSign (time (N + massSubsequence j))
          (htime_pos (N + massSubsequence j))
  obtain ⟨target, measureSubsequence, hmeasureSubsequence, hweak⟩ :=
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_tendsto_pos
      (fun j => mu (massSubsequence j)) massLimit hmassLimitPos
      collisionRankFrequencyTripleSupport
      collisionRankFrequencyTripleSupport_isCompact
      (by simpa [markedMass, Function.comp_def] using hmassTendsto) hsupport
  let subsequence : Nat -> Nat := fun j =>
    N + massSubsequence (measureSubsequence j)
  have hsubsequence : StrictMono subsequence := by
    intro i j hij
    exact Nat.add_lt_add_left
      ((hmassSubsequence.comp hmeasureSubsequence) hij) N
  have hweak' : Tendsto
      (fun j =>
        canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          ensemble decayInteractionSign (time (subsequence j))
            (htime_pos (subsequence j)))
      atTop (nhds target) := by
    simpa [mu, subsequence] using hweak
  have htargetLower : massLower <= target.mass := by
    apply ge_of_tendsto' hweak'.mass
    intro j
    rw [hmassEq (subsequence j)]
    exact (hN (subsequence j)
      (Nat.le_add_right N (massSubsequence (measureSubsequence j)))).1
  have htargetUpper : target.mass <= massUpper := by
    apply le_of_tendsto' hweak'.mass
    intro j
    rw [hmassEq (subsequence j)]
    exact (hN (subsequence j)
      (Nat.le_add_right N (massSubsequence (measureSubsequence j)))).2
  have htimeSub : Tendsto (fun j => time (subsequence j)) atTop atTop :=
    htime.comp hsubsequence.tendsto_atTop
  let collision : ResonantThreeWaveMeasure RankFrequencyMark :=
    ofCanonicalBroadenedWeakLimit ensemble
      (fun j => time (subsequence j))
      (fun j => htime_pos (subsequence j)) htimeSub target hweak'
  have hcollision : collision.collisionMeasure = target := by
    rfl
  have hcollisionLower : massLower <= collision.collisionMeasure.mass := by
    rw [hcollision]
    exact htargetLower
  have hcollisionUpper : collision.collisionMeasure.mass <= massUpper := by
    rw [hcollision]
    exact htargetUpper
  have hcollisionNonzero : collision.collisionMeasure ≠ 0 := by
    apply collision.collisionMeasure.mass_nonzero_iff.mp
    exact (hmassLower.trans_le hcollisionLower).ne'
  exact ⟨target, subsequence, collision, hsubsequence, hweak', hcollision,
    hcollisionLower, hcollisionUpper, hcollisionNonzero⟩

/-- Infinitely many positive, uniformly finite scalar broadened masses are
already enough for a nonzero on-shell marked cluster.  This is weaker than an
eventual bound: the proof first enumerates only the good observation times and
then applies the eventual two-sided criterion to that cofinal subsequence. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_frequently_scalarMass_bounds
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (massLower massUpper : NNReal) (hmassLower : 0 < massLower)
    (hmassBounds : ∃ᶠ n in atTop,
      massLower <=
          (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time n) (htime_pos n)).mass /\
        (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time n) (htime_pos n)).mass <=
          massUpper) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble decayInteractionSign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          massLower <= collision.collisionMeasure.mass /\
          collision.collisionMeasure.mass <= massUpper /\
          collision.collisionMeasure ≠ 0 := by
  let scalarMass : Nat -> NNReal := fun n =>
    (canonicalBroadenedCollisionPerSiteMeasureLimit
      ensemble decayInteractionSign (time n) (htime_pos n)).mass
  let good : Nat -> Prop := fun n =>
    massLower <= scalarMass n /\ scalarMass n <= massUpper
  have hgoodFrequently : ∃ᶠ n in atTop, good n := by
    simpa [good, scalarMass] using hmassBounds
  have hgoodInfinite : Set.Infinite {n | good n} :=
    Nat.frequently_atTop_iff_infinite.mp hgoodFrequently
  let selected : Nat -> Nat := Nat.nth good
  have hselected : StrictMono selected := by
    dsimp only [selected]
    exact Nat.nth_strictMono hgoodInfinite
  have hselectedBounds : forall n,
      massLower <=
          (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time (selected n))
              (htime_pos (selected n))).mass /\
        (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble decayInteractionSign (time (selected n))
              (htime_pos (selected n))).mass <= massUpper := by
    intro n
    have hn := Nat.nth_mem_of_infinite hgoodInfinite n
    simpa [selected, good, scalarMass] using hn
  obtain ⟨target, subsequence, collision, hsubsequence, hweak, hcollision,
      hcollisionLower, hcollisionUpper, hcollisionNonzero⟩ :=
    exists_positive_canonicalOnShellMarkedCluster_of_eventual_scalarMass_bounds
      ensemble (fun n => time (selected n))
      (fun n => htime_pos (selected n))
      (htime.comp hselected.tendsto_atTop)
      massLower massUpper hmassLower
      (Eventually.of_forall hselectedBounds)
  exact ⟨target, selected ∘ subsequence, collision,
    hselected.comp hsubsequence,
    by simpa [Function.comp_def] using hweak,
    hcollision, hcollisionLower, hcollisionUpper, hcollisionNonzero⟩

end

end ArchonPhysics.CanonicalOnShellMarkedClusterPositiveBounds
