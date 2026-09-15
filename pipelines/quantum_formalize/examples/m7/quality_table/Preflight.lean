import M7QualityTable

def Frozen_solve_distance : Prop :=
 ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M7.QualityTable.solveDistance c = M7.DefaultQuery.distance c

def Frozen_cache_action : Prop :=
 ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → ∀ g : M7.Action.Record N, (M7.DefaultQuery.dimension (M7.Action.act g c), M7.DefaultQuery.distance (M7.Action.act g c)) = M7.QualityTable.cache c

def Frozen_array_scores : Prop :=
 ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M7.QualityTable.leftTable c (g.unit,g.exchange)).size = N ∧ (M7.QualityTable.rightTable c (g.unit,g.exchange)).size = N ∧ M7.QualityTable.placedScores c g = (M7.DefaultQuery.locality (M7.Action.act g c), M7.DefaultQuery.radius (M7.Action.act g c))
