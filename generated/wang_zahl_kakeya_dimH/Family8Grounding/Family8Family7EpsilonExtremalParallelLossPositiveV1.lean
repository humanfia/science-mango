import Family4GlobalExtremalUpstream
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open scoped ENNReal NNReal

namespace Family8Family7EpsilonExtremalParallelLossPositiveV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream

noncomputable section

universe u

/-! # Positivity of the integer extremal parallel loss -/

theorem EpsilonExtremalTubeFamily.parallelLoss_pos
    {delta : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {Y : Shading fine.bodyFamily} {active : Finset iota}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily fine Y active parallelLoss
      epsilon sigma) :
    0 < parallelLoss := by
  have hpow : 0 < (delta : ENNReal) ^ (-epsilon) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr G.delta_pos) ENNReal.coe_ne_top
  have hcast : 0 < (parallelLoss : ENNReal) :=
    hpow.trans_le G.parallelLoss_rounds_power
  exact_mod_cast hcast

#print axioms EpsilonExtremalTubeFamily.parallelLoss_pos

end

end Family8Family7EpsilonExtremalParallelLossPositiveV1
