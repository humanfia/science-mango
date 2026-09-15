import M6QueryResources
#check (∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4*(2*N+1))
#check (∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000*N^3*4^R)
#check (∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192*N^2*2^R)
#check (∀ R N e : ℕ, R < N → e ≤ 180*(N+1)^3 → M6.Transfer.distanceWork R N e ≤ 50000*N^3*4^R)
#check (∀ R N e k : ℕ, R < N → e ≤ 180*(N+1)^3 → k ≤ 2*N → M6.Transfer.witnessWork R N e k ≤ 200000*N^4*4^R)
#check (∀ R N slots : ℕ, R < N → slots ≤ 256*(N+1)^2 → M6.Transfer.solveStorage R N slots ≤ 10000*N^2*2^R)
