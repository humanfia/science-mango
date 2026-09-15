# M6 Euclid live experiment

The final definition and all21 exact types passed preflight before freezing. LAUNCH.json records dag-launcher-mq6ltoi7 in /home/jing/m6-lean-euclid-formalization. Settings are gpt-6-astra medium,16 concurrency cap,5 rounds,180-second compiler and600-second model-turn limits, read-only workers, Mathlib+Physlib retrieval, exact frozen-target audit and final combined assembly.

Independent initial branches prove binary monicity/normalization, degree-rank order, remainder congruence, explicit cancellation-pass counts, range-loop cost, degree scanning and faithful array encoding. Their dependent branches prove decreasing leading-term XOR, bounded-fuel remainder correctness, Euclidean gcd correctness, telescoping cancellation and round bounds, all-intermediate width safety and exact array cancellation. They join at the cubic one-call cost and the original shared two-call gcd(a,b,M) preprocessing theorem.

The graph uses only M6Euclid definitions and the pinned Mathlib dependency. It assumes no prior M5 or M6 theorem, no proof oracle and no externally asserted complexity bound. Preflight counts zero proved targets. Successful live candidates are preserved; any later local repair must retain the exact source/type and normal acceptance checks.
