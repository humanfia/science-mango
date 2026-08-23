# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_hitting_time.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_hitting_time.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c5ba227414133ab5d7d1446b48a3accc4c97b1a55dcd3e721d7adc0b7545774e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Positive event times`
- `ArchonPhysics.HittingTime.hittingTimes` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Strictly positive times at which the event holds.
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | No strictly positive event can occur strictly before the first hitting time.
- `ArchonPhysics.HittingTime.persistenceTimes` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Strictly positive start times at which the event persists for `L`.

### Query: `First hitting infimum`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

### Query: `Persistence on a closed interval`
- `ArchonPhysics.HittingTime.persistence_spec` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The defining formulae for duration-indexed persistence times.
- `ArchonPhysics.HittingTime.persistenceTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive start time at which the event persists for `L`.
- `ArchonPhysics.HittingTime.persistenceTimes` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Strictly positive start times at which the event persists for `L`.

### Query: `An event time bounds its first hitting infimum`
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | No strictly positive event can occur strictly before the first hitting time.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.

### Query: `equilibration Times`
- `ArchonPhysics.HittingTime.hittingTimes` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Strictly positive times at which the event holds.
- `ArchonPhysics.HittingTime.persistenceTimes` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Strictly positive start times at which the event persists for `L`.
- `ArchonPhysics.HittingTime.PersistsFor` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The event holds continuously from `t` through the duration `L`.

### Query: `equilibration Hitting Time`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

### Query: `Persists For`
- `ArchonPhysics.HittingTime.PersistsFor` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The event holds continuously from `t` through the duration `L`.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform finite weights attain the maximal spectral entropy.

### Query: `hitting time physics formalization target`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.HittingTime.hittingTimes` (ArchonPhysics)
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.persistenceTimes` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.HittingTime.persistence_spec` (ArchonPhysics)
- `ArchonPhysics.HittingTime.persistenceTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.persistenceTimes` (ArchonPhysics)
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.hittingTimes` (ArchonPhysics)
- `ArchonPhysics.HittingTime.persistenceTimes` (ArchonPhysics)
- `ArchonPhysics.HittingTime.PersistsFor` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.HittingTime.PersistsFor` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.HittingTime.PersistsFor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
