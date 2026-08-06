# Five-stage campaign configurations

`five_stage_campaign.coset_two_block_actions_v2.json` is the current live
coset-action campaign. It must start with a fresh run ID and uses
`evolve/coset_config_v2.yaml` plus `evolve/coset_seed_solution_v2.py`.

`five_stage_campaign.coset_two_block_v1.json` and
`five_stage_campaign.coset_two_block_map_v2.json` are frozen historical inputs.
They remain in the repository so committed v1 transactions and artifacts can
be byte-replayed, but the current live mutation/search DSL and launcher are
v2-only. Do not use either historical file to start or resume OpenEvolve work.
