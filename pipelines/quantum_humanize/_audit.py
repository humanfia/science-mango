"""Bounded byte-reading plans and private, in-memory reviewer continuations."""

import hashlib
import shlex
from dataclasses import dataclass


@dataclass
class Continuation:
    # Never serialize a native session, transcript, or another reviewer's notes.
    worker: object = None
    session: object = None
    inputs: object = None
    manifest: object = None
    previous_call: str = ""
    keep_incomplete: bool = False

    def close(self):
        errors = []
        try:
            if self.session is not None:
                self.session.close()
        except Exception as error:
            errors.append(f"session close failed: {type(error).__name__}")
        finally:
            try:
                if self.worker is not None:
                    self.worker.stop()
            except Exception as error:
                errors.append(f"worker stop failed: {type(error).__name__}")
            self.worker = self.session = None
        return errors


def byte_ranges(data, limit=8192):
    """Exact, exhaustive UTF-8-safe chunks, including single-line JSON manuscripts."""
    data.decode("utf-8")
    if limit < 4:
        raise ValueError("chunk size must fit one UTF-8 character")
    start = 0
    while start < len(data):
        end = min(start + limit, len(data))
        while end < len(data) and data[end] & 0xC0 == 0x80:
            end -= 1
        yield [start, end - start]
        start = end


def reading_plan(candidate, manifest, read):
    """Plan direct references only; further reading follows actually invoked results."""
    entries = {entry["path"]: entry for entry in manifest["files"]}
    pending = [ref.model_dump() for ref in candidate.dependencies]
    seen, rows = set(), []
    while pending:
        ref = pending.pop(0)
        name = ref["path"]
        entry = entries.get(name)
        if entry is None or entry["sha256"] != ref["sha256"]:
            raise ValueError("unlocked audit dependency: " + name)
        if name in seen:
            continue
        seen.add(name)
        data = read(name)
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError("changed audit dependency: " + name)
        rows.append({"path": name, "sha256": entry["sha256"], "bytes": len(data),
                     "ranges": list(byte_ranges(data))})
    return rows


def read_command(path, offset, count):
    return f"dd if={shlex.quote(path)} bs=1 skip={offset} count={count} status=none"


READING_PROMPT = """
BOUNDED DEPENDENCY READING PLAN (navigation, not proof or read receipts).
Each range is [byte offset, byte count], UTF-8 safe and at most 8192 bytes.
Read ONE range per terminal call, with an output allowance of at least 16384 tokens:
  dd if='EXACT_PATH' bs=1 skip=OFFSET count=COUNT status=none
Use only if/bs/skip/count/status; never of=, redirection, or write operations.
Do not concatenate files or use line-count chunks: canonical proof JSON often
occupies one enormous line. Verify the original whole-file SHA with sha256sum.
Do not mark a file fully read until every required range has returned untruncated.
If a tool still truncates a range, split that byte range again and read both halves.
The plan covers direct references, NOT a recursive obligation to re-read all past
drafts or re-prove all their claims. Locate and check any additionally invoked dependency
or corresponding review in the frozen manifest; use the same bounded reads.
Check applicability and hypotheses of invoked results, not unrelated upstream claims.
On an unfinished audit, use inconclusive and record in repair the exact file SHA,
completed byte ranges, next unread range, and remaining applicability/claim checks.
Your own session can continue this work; no other reviewer's notes are supplied.
""".strip()
