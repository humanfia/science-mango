import M8OptimizerResourcesAccepted
namespace M8.BankLayout
/-- Input, original gcd, output witness, cutoff, selected choice, transformed input. -/
def bufferWidths (N : ℕ) : List ℕ := [2*N,N+1,2*N,N+1,1+3*(N+1),2*N]
def registers : List String :=
  ["phase","exchange","unit","leftAnchor","rightAnchor","leftCursor","rightCursor",
   "gcdP","gcdQ","gcdShift","gcdCarry","inverseP","inverseQ","inverseX","inverseY",
   "inverseShift","inverseCarry","residue","product","remainder","spanLeft","spanRight",
   "sourceAddress","targetAddress","bitCursor","wordCursor","layerCursor","startCursor",
   "queryCursor","workCounter","loopCounter","savedIndex"]
def registerBits (N : ℕ) : ℕ := 32*(N+1)
/-- Exactly the existing M6 banks at the fixed public cutoff, reused for every query. -/
noncomputable def bankSlots (N : ℕ) : ℕ :=
  M6.Transfer.solveStorage (M8.Cutoff.limit N) N (M6.EuclidStorage.actualPreprocessStorage N)
noncomputable def payloadSlots (N : ℕ) : ℕ :=
  (bufferWidths N).sum + registers.length * registerBits N + bankSlots N
end M8.BankLayout
