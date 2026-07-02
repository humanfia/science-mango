# Migrating to a newer HumanizePhysics

This guide walks you through upgrading an existing HumanizePhysics install and,
separately, an existing HumanizePhysics-initialized project. If you are starting
from scratch, you don't need this file — follow the
[README](../README.md) instead.

- **Coming from a pre-CLI checkout?** Start with section 1 (v0.1.0 reworked
  installation around a single `humanizephysics` CLI) and continue through to
  section 6.
- **Coming from v0.2.0 or earlier?** Skip to [section 8](#8-upgrading-to-v030) —
  v0.3.0 adds a configurable Claude backend for alternative headless
  entrypoints and hardens stage detection.
- **Coming from v0.1.0?** Skip to [section 7](#7-upgrading-from-v010-to-v020) —
  v0.2.0 adds multi-lane proving, the refactor agent, inner-git
  versioning, `humanizephysics-protected.yaml`, an opt-in subagent system, a
  `--resume` flag, a blueprint-doctor phase, and a post-plan validation
  step. Default single-agent behavior is preserved, so the v0.1.0 install
  you have keeps working.

## Notes for v0.1.0 readers (kept for reference)

## TL;DR

*It is always safer to backup your project before running a migration. We recommend committing all changes to git and pushing to a remote before starting. However, be aware that some files are gitignored by default (e.g. `.humanizephysics/`)*

1. **Reinstall** the tool with the new one-line installer.
2. **Re-run `humanizephysics init`** in each project that was initialized by an older
   version. When asked, pick **merge** (recommended) — HumanizePhysics will walk you
   through the differences file by file with Claude Code's help.

Your project source files (`.lean`, papers, etc.) are never touched. Only
files inside `.humanizephysics/` and project-scope Claude Code registrations are
affected.

---

## 1. What changed

### 1.1 Installation: shell scripts → Python CLI

Previous versions shipped a collection of shell scripts (`humanizephysics-loop.sh`,
`init.sh`, `review.sh`, etc.) that you ran from a cloned checkout of the
repository. v0.1.0 replaces them with a single installable Python package
that exposes the commands below:

| Command | Description |
|---------|-------------|
| `humanizephysics init` | Initialize a new HumanizePhysics project (or reconcile an existing one). |
| `humanizephysics loop` | Run the automated plan → prove → review loop. |
| `humanizephysics dashboard` | Start the web monitoring interface. |
| `humanizephysics doctor` | Verify the full HumanizePhysics setup and health. |
| `humanizephysics prove` | Directly prove an inline statement. |
| `humanizephysics setup` | Install required system dependencies. |
| `humanizephysics update` | Update HumanizePhysics to the latest published version. |

The install command is:

```bash
curl -sSL https://raw.githubusercontent.com/frenzymath/HumanizePhysics/refs/heads/main/install.sh | bash
```

You no longer need to keep a clone of the HumanizePhysics repository around to use
HumanizePhysics. The package is installed into your Python environment and can be
updated with `humanizephysics update`.

### 1.2 Project layout: symlinks → copies

Previous versions populated `<project>/.humanizephysics/prompts/` with **symlinks
back to the HumanizePhysics source checkout** and installed `lean4-skills` as a
symlinked cache. This meant:

- Changing a prompt in the HumanizePhysics repo instantly affected every project.
- Deleting or moving the HumanizePhysics checkout silently broke every project that
  was symlinked to it.

v0.1.0 uses **copies** instead. Each project gets its own independent copy
of the prompts, `AGENTS.md`, the informal agent, and the skills plugin.
This removes the fragility and lets you safely edit prompts per-project,
but it also means template updates no longer propagate automatically — you
pull them in by re-running `humanizephysics init` and choosing **merge** or
**overwrite**.

### 1.3 Dashboard: manual → auto-launch

`humanizephysics loop` now launches the web dashboard in the background on a free
port in 8080–8099 by default and prints the URL. The dashboard keeps
running after the loop finishes so you can inspect results. Pass
`--no-dashboard` to disable, or `--open` to open a browser automatically.

### 1.4 Re-init is now safer

Running `humanizephysics init` on a project that was already initialized — by this
or an older version — no longer errors or overwrites your edits silently.
It detects the existing setup and offers four choices:

- **keep** — leave files alone; just refresh MCP / plugin registrations.
- **merge** *(recommended)* — launch Claude Code in a focused diff session
  and reconcile each prompt / `AGENTS.md` file interactively.
- **overwrite** — replace all HumanizePhysics files with the bundled versions
  (discards local edits to prompts and `AGENTS.md`).
- **abort** — cancel without changes.

User state (`PROGRESS.md`, `USER_HINTS.md`, `task_pending.md`, `task_done.md`,
`proof-journal/`) is preserved in all non-abort modes.

### 1.5 MCP / plugin registration is self-healing

The old MCP registration pointed into the HumanizePhysics source checkout. If you
moved or deleted that checkout, the MCP server would silently break.
`humanizephysics init` now:

- Removes any existing `humanizephysics-lean-lsp` registration and re-adds it with
  the current install's path.
- Detects when the `humanizephysics-local` plugin marketplace points at a stale
  path and updates it.
- Disables conflicting global `lean4-skills` / `lean-lsp` plugins **for
  this project only** — your other projects are untouched.

---

## 2. Upgrading the tool

You do not need to uninstall the old scripts first — they live in your cloned checkout and are inert once you stop running them.

### 2.1 Fresh install

If you never ran HumanizePhysics via pip before:

```bash
curl -sSL https://raw.githubusercontent.com/frenzymath/HumanizePhysics/refs/heads/main/install.sh | bash
```

This fetches the repository, runs `pip install .`, and executes
`humanizephysics setup` to install system dependencies. We recommend using a
dedicated virtual environment (e.g. `python -m venv ~/.venvs/humanizephysics &&
source ~/.venvs/humanizephysics/bin/activate`) before running the installer.

### 2.2 If you already installed a preview CLI build

If you installed one of the preview builds from the PR branch, update with:

```bash
humanizephysics update
```

This re-runs the installer against `main`.

### 2.3 Verify the install

```bash
humanizephysics -h
humanizephysics doctor
```

If `humanizephysics doctor` is happy, you're ready to migrate your projects.

---

## 3. Upgrading an existing project

Do this for each project where you previously ran the old `init.sh`.

### 3.1 Before you start

**Backup, commit and push your project.** Both the recommended merge flow and the
fallback overwrite flow only touch `.humanizephysics/` and your project-scope Claude
Code registrations, not your `.lean` files — but you should have a clean
checkpoint anyway before running any tool that edits project state.

Commit `lean` files:

```bash
cd /path/to/your-lean-project
git add .
git commit -m "Backup before HumanizePhysics CLI migration"
git push
```

Back-up `.humanizephysics/` state files:

```bash 
cp -r .humanizephysics/ .humanizephysics-backup/
```

If you have customizations under `.humanizephysics/prompts/` or in `.humanizephysics/AGENTS.md`
that you want to keep, be aware that currently `.humanizephysics/` is gitignored.

### 3.2 Run `humanizephysics init`

```bash
humanizephysics init /path/to/your-lean-project
```

HumanizePhysics detects the existing setup and prints something like:

```
⚠ This project has already been initialized with HumanizePhysics.
  Detected layout:        legacy-symlink
  Current stage:          prover
  Prompts are symlinks:   yes

Detected the legacy symlink-based layout. The new CLI copies prompts
into .humanizephysics/prompts/ instead of symlinking. Re-initializing directly
would break the old symlinks.

How would you like to proceed?
  [k] keep
  [m] merge      (recommended)
  [o] overwrite
  [a] abort
```

The right choice depends on what you've edited:

| Situation | Choose |
|-----------|--------|
| You never edited anything under `.humanizephysics/prompts/` or `.humanizephysics/AGENTS.md`. | **overwrite** |
| You edited some prompts and want to review the differences. | **merge** |
| You want to keep your current setup and only refresh registrations. | **keep** |
| You are not sure. | **merge** |

### 3.3 The merge flow in detail

When you pick `merge`, HumanizePhysics:

1. Copies the new bundled prompts and `AGENTS.md` to a staging directory
   (`.humanizephysics/.humanizephysics-incoming/`).
2. Launches Claude Code with a focused prompt.
3. For every file that differs, Claude summarizes the changes and asks you
   to choose:
   - `[L]` keep your local version
   - `[N]` take the new bundled version
   - `[M]` merge manually — Claude writes a proposed merge and stops so you
     can review it in your editor
4. Cleans up the staging directory when done.

Claude is instructed to never touch `PROGRESS.md`, `USER_HINTS.md`,
`task_pending.md`, `task_done.md`, `proof-journal/`, or any `.lean` file.
Only prompts and `AGENTS.md` are in scope.

If Claude Code is not installed (it should be, if `humanizephysics setup` succeeded),
the merge step falls back to a text-only diff summary.

### 3.4 After init completes

`humanizephysics init` will:

- Finish by running `/humanizephysics-lean4:doctor` to verify Lean, MCP, and skills
  are healthy.
- Print the next step: `humanizephysics loop /path/to/your-lean-project`.

You can now run the loop as usual.

---

## 4. Things you can safely delete

Once the new CLI is installed and your projects have been re-initialized,
the following are no longer needed and can be removed:

- Your old HumanizePhysics source checkout (if you installed via `pip install .`
  from it, the package has been copied into your Python environment — the
  checkout itself is no longer referenced).
- Any shell aliases or scripts that called `humanizephysics-loop.sh`, `init.sh`, or
  `review.sh` directly.
- The `.humanizephysics/prompts/` directory content *in projects you have already
  migrated* — but leave the directory itself alone; `humanizephysics init` manages
  it. (If you're worried, just leave it; stale symlinks are cleaned up on
  the next `init`.)

Do **not** delete `<project>/.humanizephysics/PROGRESS.md`,
`<project>/.humanizephysics/USER_HINTS.md`, `<project>/.humanizephysics/task_*.md`, or
`<project>/.humanizephysics/proof-journal/` — these contain your formalization state.

---

## 5. Troubleshooting

### `humanizephysics: command not found` after install

The `install.sh` script runs `pip install .` into whichever Python
environment is active when you invoke it. If you ran it inside a venv,
`humanizephysics` is only on your PATH when that venv is active. Activate it, or
install into a more permanent location and ensure that location's `bin/`
is on your PATH.

### `Claude Code is not installed`

Run `humanizephysics setup` — it will install `uv` and Claude Code and verify your
Lean toolchain. By default it asks before running `sudo`; pass `--yes` to
accept automatically.

### Merge mode shows "Claude Code is not installed — falling back to a text-only diff summary"

Install Claude Code via `humanizephysics setup`, then re-run `humanizephysics init` and
choose **merge** again.

### `humanizephysics-lean-lsp` does not appear in `claude mcp list`

Run `humanizephysics init` again. v0.1.0 explicitly removes and re-adds the
registration so the path always points at the current install.

### The dashboard did not start

Check that Node.js and npm are installed (run `humanizephysics setup` if not), and
that at least one port in 8080–8099 is free. If neither applies, pass
`--no-dashboard` to `humanizephysics loop` and start it manually in another
terminal with `humanizephysics dashboard /path/to/your-lean-project`.

### I accidentally chose overwrite and lost my prompt edits

If you committed your project before migrating (section 3.1), please note that `.humanizephysics` is gitignored by default, so you should create a backup beforehand if you want to recover your old prompts.

### I initialized successfully but the loop complains about the stage being "init"

The interactive init step did not complete. Re-run `humanizephysics init` and make
sure to finish the Claude Code session (it will ask you to confirm initial
objectives and then write them to `PROGRESS.md`).

---

## 6. Rolling back

If the migration goes sideways and you want to return to the previous
state of a project:

```bash
cd /path/to/your-lean-project
cp -r .humanizephysics-backup/ .humanizephysics/
```

Where `.humanizephysics-backup/` is a copy of `.humanizephysics/` from before the migration. Note that by default `.humanizephysics/` is gitignored.
The MCP and plugin registrations can be refreshed by running
the old `init.sh` again from your former HumanizePhysics checkout, or by
re-running `humanizephysics init` and picking **keep**.

To roll back the tool install itself:

```bash
pip uninstall humanizephysics
```

Then reinstall whichever version you were on previously.

---

## 7. Upgrading from v0.1.0 to v0.2.0

v0.2.0 adds multi-lane proving, the refactor agent, inner-git versioning of
agent work, and a frozen-signature surface (`humanizephysics-protected.yaml`). Most of
this is transparent — your existing v0.1.0 projects keep working — but a few
things are worth doing once per project to pick up the new behaviour.

### 7.1 Reinstall the CLI

```bash
humanizephysics update
```

If you originally installed without `humanizephysics update` available, run the
one-line installer again — it is idempotent.

### 7.2 Re-run `humanizephysics init` in each project (recommended)

The prompts and `AGENTS.md` template gained several pieces of guidance in
v0.2.0 — iteration-number canonicalization, LaTeX-macro hygiene, and a rule
against listing off-limits files in `## Current Objectives`. The plan agent
also now picks up the bundled dependency-graph script. To pull these into a
project initialised under v0.1.0:

```bash
humanizephysics init /path/to/your-lean-project
```

Pick **merge** (recommended) — HumanizePhysics walks you through the diffs file by
file. Your `PROGRESS.md`, `task_*.md`, `proof-journal/`, and `.lean` files
are never touched.

### 7.3 New files inside `.humanizephysics/` after v0.2.0 init

| File | What it is | Edit? |
|------|------------|------|
| `.humanizephysics/git-dir/` | Inner git repo. Every agent phase commits here as `humanizephysics[NNN/phase]`. | No — managed by HumanizePhysics. |
| `.humanizephysics/config.json` | Per-project loop and multilane settings. Versioned with your project. | Yes — see [MULTILANE.md](MULTILANE.md). |
| `.humanizephysics/.env` | API keys for the informal agent and multilane providers. | Yes — gitignored, never commit. |
| `.humanizephysics/REFACTOR_DIRECTIVE.md` | Where the plan agent writes refactor directives. Cleared after each refactor pass. | Plan agent writes; you can read for context. |
| `.humanizephysics/STRATEGY.md` | Plan agent's living long-arc plan. | Plan agent owns; you can read. |
| `.humanizephysics/VERSION` | Stamped at init time so re-init knows what version produced the project. | No. |

### 7.4 New file at the project root: `humanizephysics-protected.yaml`

If you want to freeze certain declaration signatures from agent edits, add
them here. Example:

```yaml
src/MyProject/Core.lean:
  - main_theorem
  - key_definition
```

Agents will refuse to rename or re-sign listed declarations. The refactor
agent may move them between files (and update the file path key in this
yaml) but cannot otherwise touch them. The file is committed to the project
git so the whole team shares the protected surface.

`humanizephysics init` writes an empty `humanizephysics-protected.yaml` if none exists; fill it
in when you are ready.

> **v0.3.0 extends this format.** The flat form above still works, but you can
> now also protect blueprint (`.tex`) files and `\label{}` blocks, choose a
> protection level (freeze the signature/statement vs. the whole declaration),
> and use glob patterns. See the README's `humanizephysics-protected.yaml` section.

### 7.5 The CLI gained four commands

| Command | What it does |
|---------|--------------|
| `humanizephysics refactor run /path/to/project` | Execute the refactor agent against the directive in `.humanizephysics/REFACTOR_DIRECTIVE.md`. Create that directive interactively first with `humanizephysics refactor draft /path/to/project`. |
| `humanizephysics discuss /path/to/project` | Open Claude Code interactively with full HumanizePhysics context loaded — for debugging or brainstorming without firing the loop. |
| `humanizephysics branch <name> /path/to/project --from <commit>` | Create a new branch in the inner git from a historical agent commit (e.g. before a bad refactor). Without `--from`, switches to an existing branch named `<name>`. |
| `humanizephysics version /path/to/project` | Show the HumanizePhysics CLI version and, in a project, the project version. |

### 7.6 Enabling subagents (optional)

v0.2.0 introduces an opt-in **subagent system** — descriptor-driven
helpers the plan / review agent can dispatch when it needs a focused,
fresh-context check. **All ship disabled** so the loop behaves exactly as
it did in v0.1.0 unless you opt in. To turn one or more on, edit
`.humanizephysics/config.json`:

```json
"subagents": {
  "enabled": ["strategy-critic", "blueprint-reviewer", "progress-critic"]
}
```

The shipped `config.json` includes an `_available` list naming every
shipped subagent; copy any of them into `enabled`. Recommended starting
sets:

- **Plan phase**: `blueprint-reviewer`, `strategy-critic`, `progress-critic`
- **Review phase**: `lean-auditor`, `lean-vs-blueprint-checker`

Subagents with `mandatory: [<phase>]` in their frontmatter must be
dispatched at least once when enabled. The plan / review prompts surface
them with a `[MANDATORY]` tag and a post-phase audit warns (does not
abort) when one is missed. With every subagent disabled, the catalog is
empty and no mandatory dispatch is ever required.

To enable every shipped subagent at once, copy the entire `_available`
list into `enabled`.

### 7.7 `max_parallel` default lowered from 8 to 4

Fresh projects pick up `max_parallel: 4` in `.humanizephysics/config.json`.
**Existing projects keep whatever value they already have** — re-running
`humanizephysics init` with `keep` or `merge` preserves your current setting. To
restore v0.1.0 behavior on a fresh project, either set:

```json
"loop": { "max_parallel": 8 }
```

or pass `--max-parallel 8` on the command line.

### 7.8 `ui/start.sh` removed

If you previously launched the dashboard via `ui/start.sh`, use the CLI
instead:

```bash
humanizephysics dashboard /path/to/your-lean-project
```

(`humanizephysics loop` already auto-launches it — this only matters if you were
starting the dashboard standalone.)

### 7.9 New `--resume` flag

| Flag | What it does |
|------|--------------|
| `--resume` | When a previous `humanizephysics loop` was interrupted mid-iteration, resume the in-flight iteration at its last completed phase. The phase is auto-detected from `.humanizephysics/logs/iter-NNN/meta.json`. |

### 7.10 New blueprint-doctor phase

Runs automatically each iteration, between the prover and review phases
(right after the deterministic `\leanok` sync). It scans `blueprint/src/`
for orphan chapters, broken `\ref{...}` / `\uses{...}` / `\cref{...}`
references, malformed (empty) annotations, stray `axiom` declarations, and
`% humanizephysics:covers` integrity problems, writing a report to
`.humanizephysics/logs/iter-NNN/blueprint-doctor.{md,json}`. The same iteration's
review agent reads the report, and the next iteration's plan agent sees the
findings inline under `## Blueprint doctor — live structural findings`. No
configuration is needed — it's silently included in every iteration.

---

## 8. Upgrading to v0.3.0

v0.3.0 adds a **modular engine system** (run roles/subagents on Claude Code or
**OpenAI Codex** via named harnesses; pick a Claude **backend**, including the
`claude-p` workaround for Anthropic's headless `claude -p` rate limits), the
**`humanizephysics dag`** blueprint-writing loop grounded in
[LeanDag](https://github.com/AxelDlv00/LeanDAG), **prover modes**,
`humanizephysics extract`/`merge`, new dashboard views, and more. Most of it is opt-in —
the default single-lane Claude Code loop is unchanged. The full feature list is
in [CHANGELOG.md](CHANGELOG.md); the steps below are everything you must *do* to
upgrade (almost all automatic).

### 8.1 Reinstall the CLI

```bash
humanizephysics update
```

### 8.2 Modular engine system: harnesses + Claude backends

v0.3.0 makes the engine that runs each role/subagent configurable. Two knobs:

- **Harness** — *which* engine runs the work: the built-in Claude Code, or
  **OpenAI Codex**. Set one harness for everything in one line
  (`loop.harness: "codex"`), per role (`loop.roles.<plan|prover|review>`), or
  per subagent (`subagents.<name>.harness`).
- **Claude backend** — *how* the Claude engine is launched, via
  `--claude-backend` or `loop.claude_backend`:
  - `default`: plain `claude -p`
  - `vscode` / `desktop`: sets `CLAUDE_CODE_ENTRYPOINT` accordingly
  - `claude-p`: drives the Claude Code TUI headlessly via the
    [claude-p](https://github.com/AxelDlv00/claude-p) wrapper — the recommended
    workaround now that Anthropic rate-limits headless `claude -p` on
    subscription plans
  - `interactive`: foreground, human-driven (forces serial, disables multilane)

The backend now also propagates to subagents automatically. See the full
reference in **[docs/CONFIGURATION.md](CONFIGURATION.md)**.

### 8.3 Blueprint DAG loop (`humanizephysics dag`)

`humanizephysics dag` is a new, optional loop that writes a coherent LeanBlueprint
dependency graph before (or partway through) the main proving loop. It grounds
the planner and provers in the project's real DAG via the
[leandag](https://github.com/AxelDlv00/LeanDAG) API rather than the LLM's fuzzy
internal picture. **No action needed to upgrade**; run `humanizephysics dag <project>`
when you want it (recommended at least once before `humanizephysics loop`, especially for
projects starting from informal notes). See the README for details.

### 8.4 Hardened stage detection

Stage detection in `PROGRESS.md` is now more resilient. Human or agent
annotations (e.g., dates or iteration numbers) appended after the stage token
are ignored by the orchestrator, preventing the loop from stalling on
unexpected input.

### 8.5 `.humanizephysics/CLAUDE.md` renamed to `.humanizephysics/AGENTS.md`

The bundled agent role doc is now `AGENTS.md` — the cross-tool convention
auto-loaded by both Claude Code and Codex (which HumanizePhysics also references
explicitly in every prompt). **No action needed:** `humanizephysics init` / `humanizephysics
update` removes the old `.humanizephysics/CLAUDE.md` and writes `.humanizephysics/AGENTS.md` for
you. The file is a bundled reference, not a user-edited file, so nothing custom
is lost. If you kept your own notes elsewhere, they're untouched.

### 8.6 Automated validation notes moved out of `USER_HINTS.md`

`USER_HINTS.md` is now strictly user-authored: the loop never writes to it.
Automated plan-validation feedback (dropped/blocked/deferred objectives,
format corrections) now lands in a separate, loop-managed `.humanizephysics/AUTO_NOTES.md`
that is captured into the plan prompt and cleared each iteration.

---

## Questions or issues

Please open an issue on the
[HumanizePhysics repository](https://github.com/frenzymath/HumanizePhysics/issues) and
describe what you ran, what you expected, and what you saw. Include the
output of `humanizephysics doctor` if possible.