# Results Directory

This directory contains the verified catalogs, simulation outputs, ablation data, and evolution artifacts used by the paper.

## Catalogs

| File | Contents | Notes |
|------|----------|-------|
| `ilp_catalog.json` | 97 BLISS-distinct CSS BB codes | MILP distances; exact where solver optimality was certified, otherwise incumbent upper bounds. |
| `campaign7_publication_merged.jsonl` | 368 BLISS-distinct non-CSS PBB codes | Canonical PBB catalog. `d` is the publication distance value; `d_is_exact`/`trust_level` distinguish exact distances from trusted or partial upper bounds. Deep MILP evidence is retained as `d_deep_milp` where available. |
| `campaign7_deep_milp.jsonl` | Deep MILP pass over 149 PBB catalog entries | Includes per-logical incumbent/optimality details and downward corrections. |
| `campaign7_dedup.jsonl` | BLISS-deduplicated PBB candidates before publication re-verification | Useful for reproducing the Campaign 5 verification pipeline. |

Current PBB accounting from `campaign7_publication_merged.jsonl`: 368 rows, 251 EXACT, 110 TRUSTED, 7 PARTIAL.

## Simulation Data

| File | Contents |
|------|----------|
| `threshold_simulation.json` | CSS X-only code-capacity simulations. |
| `threshold_simulation_milp.json` | Additional Campaign 4 CSS simulation rows. |
| `threshold_simulation_noncss.json` | PBB X-only simulations for n <= 144 rows. |
| `threshold_simulation_depolarizing.json` | PBB depolarizing simulations for n <= 144 rows. |
| `threshold_simulation_360_12_20_depol.json` | PBB `[[360,12,<=20]]` depolarizing simulation. |
| `threshold_simulation_360_12_24_depol.json` | PBB `[[360,12,<=24]]` depolarizing simulation. |
| `threshold_simulation_360_12_24.json` | PBB `[[360,12,<=24]]` X-only simulation. |
| `threshold_simulation_missing.json` | Gap-filling CSS and PBB simulation rows. |

## Verification And Analysis

| File | Contents |
|------|----------|
| `soak_test_publication.json` | Campaign 1 CSS 150k-trial multi-decoder verification. |
| `ensemble_verification_150k.json` | Campaigns 2-3 CSS 150k-trial verification. |
| `ensemble_verification_60k.json` | First-round Campaigns 2-3 CSS verification. |
| `extended_verification_1500k.json` | Extended 1.5M-trial BP-OSD checks. |
| `gross_verification_1500k.json` | Gross-code 1.5M-trial BP-OSD check. |
| `bravyi_verified.json` | Re-verification of Bravyi baseline codes. |
| `milp_optimality_audit.json` | Per-logical MILP optimality audit for headline CSS rows. |
| `per_batch_distributions.json` | Decoder batch-distribution data. |
| `ablation_k_only.json` | k-only ablation table source. |
| `ablation_study.json` | Original ablation outputs. |
| `ablation_ga_generators.json` | GA-on-generators ablation outputs. |
| `milp_ga_codes.json` | MILP verification of GA-discovered codes. |

## Evolution Artifacts

| Directory | Campaign |
|-----------|----------|
| `evolution_gemini3flash_seed42/` | Campaign 1 CSS run. |
| `evolution_ensemble1_pop100/` | Campaign 2 CSS run. |
| `evolution_ensemble2_pop1000/` | Campaign 3 CSS run. |
| `evolution_ansatz_campaign4/` | Campaign 4 CSS mixed-monomial run. |
| `evolution/campaign7/` | Campaign 5 PBB run used for the publication catalog. |

Generated runtime files from new searches should go under the existing run/checkpoint directories or a new results file with the producing script recorded in the top-level README table-source inventory.
