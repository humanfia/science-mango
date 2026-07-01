#!/usr/bin/env python3
"""
Archon Code Snapshot Hook

PostToolUse hook for Edit|Write — captures file snapshots
after each successful code edit by a prover agent.

Receives JSON on stdin from Claude Code:
{
  "session_id": "...",
  "tool_name": "Edit",
  "tool_input": { "file_path": "...", "old_string": "...", "new_string": "..." },
  "tool_response": "The file ... has been updated successfully."
}

Environment variables (set by archon-loop.sh):
  ARCHON_SNAPSHOT_DIR  — snapshot directory
    - parallel/single-file: .archon/logs/iter-NNN/snapshots/Hcju_Jensen_Construction
    - serial (--serial):    .archon/logs/iter-NNN/snapshots (root; subdir derived from file_path)
  ARCHON_PROVER_JSONL  — path to the prover's jsonl log file
  ARCHON_PROJECT_PATH  — absolute path to the lean project
  ARCHON_SERIAL_MODE   — "true" if running in --serial mode (multi-file prover)

If ARCHON_SNAPSHOT_DIR is not set, the hook exits silently (backward compat).
"""

import json
import os
import shutil
import sys
import datetime
import glob


def main():
    snap_dir = os.environ.get("ARCHON_SNAPSHOT_DIR", "")
    if not snap_dir:
        return  # Not configured — silent no-op

    prover_jsonl = os.environ.get("ARCHON_PROVER_JSONL", "")
    project_path = os.environ.get("ARCHON_PROJECT_PATH", "")
    serial_mode = os.environ.get("ARCHON_SERIAL_MODE", "") == "true"

    # Read JSON from stdin
    try:
        raw = sys.stdin.read()
        inp = json.loads(raw)
    except (json.JSONDecodeError, Exception):
        return

    tool_name = inp.get("tool_name", "")
    tool_input = inp.get("tool_input", {})
    tool_response = str(inp.get("tool_response", ""))
    file_path = tool_input.get("file_path", "")

    # Only snapshot .lean file edits that succeeded
    if not file_path.endswith(".lean"):
        return
    # Reject known failure patterns rather than matching success strings —
    # Claude Code may change wording, but errors consistently use <tool_use_error>.
    if not tool_response or "tool_use_error" in tool_response:
        return

    # Resolve relative paths against project root (Claude Code may emit relative paths)
    if not os.path.isabs(file_path) and project_path:
        file_path = os.path.join(project_path, file_path)

    # Determine the actual snapshot directory
    if serial_mode and project_path:
        # In serial mode, ARCHON_SNAPSHOT_DIR is the root snapshots/ dir.
        # Derive subdirectory from relative file path (same slug logic as archon-loop.sh).
        try:
            rel = os.path.relpath(file_path, project_path)
        except ValueError:
            rel = os.path.basename(file_path)
        slug = rel.replace("/", "_").replace(os.sep, "_")
        if slug.endswith(".lean"):
            slug = slug[:-5]
        actual_snap_dir = os.path.join(snap_dir, slug)
    else:
        actual_snap_dir = snap_dir

    # Create snapshot directory
    os.makedirs(actual_snap_dir, exist_ok=True)

    # Determine step number from existing snapshots.
    # Use O_CREAT|O_EXCL to atomically claim the step file — if two hooks race,
    # the loser bumps to the next number instead of overwriting.
    step = len(glob.glob(os.path.join(actual_snap_dir, "step-*.lean"))) + 1
    for _ in range(10):  # retry up to 10 times on collision
        step_padded = f"{step:03d}"
        step_file = os.path.join(actual_snap_dir, f"step-{step_padded}.lean")
        try:
            fd = os.open(step_file, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.close(fd)
            break  # claimed successfully
        except FileExistsError:
            step += 1
    else:
        return  # gave up after 10 collisions (shouldn't happen)

    # Copy the current file state as snapshot
    if not os.path.isfile(file_path):
        return
    try:
        shutil.copy2(file_path, step_file)
    except OSError:
        return

    # Compute relative path for logging
    rel_path = file_path
    if project_path:
        try:
            rel_path = os.path.relpath(file_path, project_path)
        except ValueError:
            pass

    # Extract edit info for the log
    old_string = tool_input.get("old_string", "")
    new_string = tool_input.get("new_string", "")
    if tool_name == "Write":
        new_string = tool_input.get("content", "")

    # Truncate for log readability (keep under PIPE_BUF for atomic writes)
    old_trunc = old_string[:200] if old_string else ""
    new_trunc = new_string[:200] if new_string else ""

    snap_dir_name = os.path.basename(actual_snap_dir)
    snap_rel = f"snapshots/{snap_dir_name}/step-{step_padded}.lean"

    # Append code_snapshot event to the prover's JSONL log
    if prover_jsonl:
        row = {
            "ts": datetime.datetime.now(datetime.timezone.utc)
            .isoformat()
            .replace("+00:00", "Z"),
            "event": "code_snapshot",
            "step": step,
            "file": rel_path,
            "tool": tool_name,
            "snapshot_path": snap_rel,
            "old_string": old_trunc,
            "new_string": new_trunc,
        }
        try:
            with open(prover_jsonl, "a") as f:
                f.write(json.dumps(row) + "\n")
                f.flush()
        except OSError:
            pass


if __name__ == "__main__":
    main()
