import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FullConvexMaximalDensity
open GreedyOccurrenceFactorization
open GreedyDensityBucketing

noncomputable section

/-!
# Frostman certificates for every greedy occurrence

The all-occurrence block theorem already follows recursively from the actual
greedy certificate.  This file bridges it to every active coarse fiber of the
occurrence-indexed convex factorization and packages the bridge with genuine
greedy existence.  No Frostman certificate is supplied as an input field.
-/

namespace GreedyAllOccurrenceFrostman

/-- Every actual occurrence block, including an arbitrarily late one, is a
constant-one Frostman family inside its own winning hull. -/
theorem every_block_isFrostmanOn_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k : Fin (blocks F P).length) :
    IsFrostmanOn 1 F (blockAt F P k).fiber (blockAt F P k).body :=
  blockAt_isFrostmanOn_one_of_subset F base P hactive k

/-- The occurrence family itself carries the same certificate at every
occurrence index. -/
theorem occurrenceFamily_isFrostmanOn_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) (k : Fin (blocks F P).length) :
    IsFrostmanOn 1 F (blockAt F P k).fiber (occurrenceFamily F P k) := by
  simpa [occurrenceFamily] using
    every_block_isFrostmanOn_one F base P hactive k

/-- Every active coarse index of the assembled occurrence-indexed convex
factorization has a genuine constant-one Frostman fiber certificate.  The
inactive `none` marker is excluded exactly by coarse activity. -/
theorem convexFactorization_activeCoarse_fiber_isFrostmanOn_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (base : Finset ι) {active : Finset ι}
    (P : GreedyDensityPartition F (hullCandidates base) (hullContainer F) active)
    (hactive : active ⊆ base) :
    ∀ k ∈ (convexFactorization F P).index.coarse,
      IsFrostmanOn 1 F
        ((convexFactorization F P).index.fiber k)
        (coarseFamily F P k) := by
  intro k hk
  change k ∈ (indexFactorization F P).coarse at hk
  rw [indexFactorization_coarse, occurrenceIndices] at hk
  obtain ⟨q, _hq, hkq⟩ := Finset.mem_image.mp hk
  subst k
  change IsFrostmanOn 1 F
    ((indexFactorization F P).fiber (some q))
    (coarseFamily F P (some q))
  rw [indexFactorization_fiber_eq_blockAt]
  change IsFrostmanOn 1 F (blockAt F P q).fiber (blockAt F P q).body
  exact every_block_isFrostmanOn_one F base P hactive q

/-- Full-convex greedy existence constructs an occurrence-indexed
factorization whose every active coarse fiber is Frostman.  The certificate
is derived after constructing the partition, rather than stored in it. -/
theorem exists_occurrenceFactorization_allFibers_isFrostmanOn_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ConvexFamily ι) (active : Finset ι) :
    ∃ P : GreedyDensityPartition F
        (hullCandidates active) (hullContainer F) active,
      P.coveredIndices = active ∧
      P.length ≤ active.card ∧
      (convexFactorization F P).index.fine = active ∧
      ∀ k ∈ (convexFactorization F P).index.coarse,
        IsFrostmanOn 1 F
          ((convexFactorization F P).index.fiber k)
          (coarseFamily F P k) := by
  obtain ⟨P, hcovered, hlength, _hglobal⟩ :=
    exists_fullConvexGreedyDensityPartition F active
  refine ⟨P, hcovered, hlength, rfl, ?_⟩
  exact convexFactorization_activeCoarse_fiber_isFrostmanOn_one
    F active P (fun _ hi => hi)

end GreedyAllOccurrenceFrostman

end

end Submission.Kakeya.ConvexFactoring
