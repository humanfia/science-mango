# Retrieval retry

The initial batch accepted four proofs and compiled their union. The other two did not reach proof generation: LeanExplore returned HTTP429 and HTTP500, and fallback also hit429. The first receipts and successful proofs remain in experiments/initial_retrieval_failure.

Retry uses the exact same graph and statements. The runner now caches successful identical queries within the experiment and serializes retrieval, while retaining proof concurrency16. Cached responses explicitly reference their source node and receipt hash; failures are not cached or treated as successful results.
