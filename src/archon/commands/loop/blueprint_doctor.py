"""Blueprint-doctor: deterministic structural lints for the project blueprint.

Four classes of bug that the doctor catches deterministically — all
cheap to detect and dramatically more reliable than asking an LLM to
notice them every iter:

1. **Orphan chapters** — ``.tex`` files under ``blueprint/src/chapters/``
   that are NOT ``\\input`` 'd by ``blueprint/src/content.tex`` (directly
   or transitively). These never appear in the rendered output yet
   continue to consume reviewer attention.

2. **Broken cross-references** — ``\\ref{<label>}`` / ``\\eqref{...}`` /
   ``\\cref{...}`` / ``\\uses{...}`` etc. whose target label is not
   defined in any included chapter. These corrupt the dependency graph
   silently — leanblueprint will draw a broken edge or none at all.

3. **Malformed annotations** — ``\\uses{}`` / ``\\proves{}`` /
   ``\\label{}`` / ``\\ref{}`` with empty argument, plus empty list
   items inside otherwise-valid ``\\uses{a,,b}``. These crash plastex
   (``Label '' could not be resolved`` followed by a depgraph
   RecursionError) without ever reaching the LLM reviewer, so detecting
   them statically is the only way to keep them out of the loop.

4. **New axiom introductions** — ``axiom`` declarations under the
   project's ``.lean`` files (excluding ``.lake``/``.archon``). Archon's
   stance is "no new axioms"; finding any is a red flag that earns a
   review-phase callout.

5. **Physics grounding evidence gaps** — physics chapters marked
   ``% archon:physics`` whose existing Lean target lacks the required
   ``task_results`` LeanExplore grounding log. This is the physics analogue
   of the structural checks above: the model may still compile, but the
   review phase needs evidence that Mathlib/PhysLean grounding was attempted.

6. **Physics contract gaps** — conservative checks for load-bearing opaque
   predicates that are only existentially witnessed, and paired experimental
   uncertainties omitted from a central-value error-band theorem contract.

The doctor is *informational*. It writes a Markdown report to
``.archon/logs/iter-NNN/blueprint-doctor.md`` and a structured JSON to
``.archon/logs/iter-NNN/blueprint-doctor.json``. The loop's phase wrapper
surfaces a one-line summary; nothing is mutated.

Run from the loop (between the prover and review phases, alongside
``sync_leanok``) so the review agent and the next iter's plan agent both
see a fresh report.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

import typer


_INPUT_RE = re.compile(r"\\(?:input|include)\s*\{\s*([^{}]+?)\s*\}")
# ``*`` (not ``+``) on the inner class so empty ``\label{}`` matches and
# is routed to ``malformed_refs``. The non-empty case continues to feed
# ``labels_defined`` unchanged.
_LABEL_RE = re.compile(r"\\label\s*\{\s*([^{}]*?)\s*\}")
# An `axiom` declaration at the start of a line (after optional whitespace
# and visibility modifiers). The doctor's caller filters out the audit's
# own snapshot tree, but we also guard against the keyword appearing in
# code comments by stripping single-line ``--`` and Lean block comments
# inside ``_count_axioms``.
_AXIOM_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+)*axiom\s+([\w.\']+)',
    re.MULTILINE,
)
_PHYSICS_MARKER = "% archon:physics"
_PHYSICS_SCALAR_FALLBACK_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:abbrev|def)\s+([A-Za-z_][\w.']*)\b"
    r"[^:\n]*:=\s*(ℝ|Real)\b",
    re.MULTILINE,
)
_LEAN_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_./']+)", re.MULTILINE)
_PHYSICS_SELF_CONTAINED_PATTERNS: tuple[tuple[str, re.Pattern[str], str], ...] = (
    (
        "self-contained-physics-file",
        re.compile(
            r"intentionally self-contained|smoke-test file|does not expose\s+"
            r"(?:PhysLean/Mathlib|Mathlib/PhysLean|Physlib/Mathlib|Mathlib/Physlib)",
            re.IGNORECASE,
        ),
        "file declares itself self-contained instead of using the real Lake "
        "Mathlib/Physlib environment",
    ),
    (
        "physics-scalar-class",
        re.compile(r"^\s*class\s+PhysicsScalar\b", re.MULTILINE),
        "defines a local scalar algebra interface; physics targets must use "
        "Mathlib's real/ordered-field hierarchy and Physlib models where "
        "available",
    ),
    (
        "local-dimension-tags",
        re.compile(r"^\s*(?:inductive\s+Dimension|structure\s+Quantity)\b", re.MULTILINE),
        "defines a local tag-only dimension/quantity system; use Physlib "
        "units/dimensions or a justified typed local model",
    ),
    (
        "symbolic-positivity-tag",
        re.compile(r"^\s*def\s+PositiveScalar\b", re.MULTILINE),
        "defines positivity as a local tag over an unconstrained scalar type; "
        "use the ordered structures from Mathlib/Physlib",
    ),
    (
        "asymptotic-tag-fallback",
        re.compile(
            r"^\s*(?:inductive\s+(?:AsymptoticRegime|TaylorOrder)|"
            r"structure\s+FirstOrderRatio)\b",
            re.MULTILINE,
        ),
        "models asymptotics/Taylor order as finite tags rather than Mathlib "
        "limits, derivatives, filters, asymptotics, or explicit hypotheses",
    ),
    (
        "jacobian-record-fallback",
        re.compile(r"^\s*structure\s+CartesianFieldJacobian\b", re.MULTILINE),
        "models a Jacobian as an unrelated record of numbers instead of "
        "derivatives of a field map",
    ),
)
_PHYSICS_QUANTITY_NAME_PARTS = (
    "charge",
    "current",
    "force",
    "field",
    "radius",
    "length",
    "distance",
    "potential",
    "voltage",
    "energy",
    "mass",
    "time",
    "velocity",
    "acceleration",
    "pressure",
    "temperature",
    "torque",
    "momentum",
    "power",
    "work",
    "capacitance",
    "resistance",
    "inductance",
)
_PHYSICS_GROUNDING_REQUIRED_TERMS = (
    ("LeanExplore mention", ("leanexplore", "lean-explore")),
    ("query/candidate evidence", ("query", "queries", "candidate", "candidates")),
    ("grounded-name section", ("grounded", "grounded names", "physlean/mathlib")),
    ("local-abstraction section", ("local abstraction", "local abstractions")),
    ("grounding-gap section", ("grounding gap", "grounding gaps")),
)
_PHYSICS_PROP_FIELD_RE = re.compile(
    r"^[ \t]+([a-z][A-Za-z0-9_']*)[ \t]*:[^\n]*(?:→|->)[ \t]*Prop[ \t]*$",
    re.MULTILINE,
)
_PHYSICS_STRUCTURE_FIELD_RE = re.compile(
    r"^[ \t]{2}[A-Za-z_][A-Za-z0-9_']*[ \t]*:",
    re.MULTILINE,
)
_PHYSICS_LOAD_BEARING_PREDICATE_PARTS = (
    "asymptotic",
    "boundary",
    "collision",
    "constraint",
    "critical",
    "equilibrium",
    "extremal",
    "incidence",
    "limiting",
    "optimal",
    "reflection",
    "tangent",
    "turning",
)
_PHYSICS_REAL_FIELD_RE = re.compile(
    r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
    r"[ \t]*:[ \t]*(?:ℝ|Real)[ \t]*$",
    re.MULTILINE,
)
_LEAN_THEOREM_HEADER_RE = re.compile(
    r"^[ \t]*(?:theorem|lemma)[ \t]+[A-Za-z_][A-Za-z0-9_.']*.*?:=[ \t]*by",
    re.MULTILINE | re.DOTALL,
)
_LEAN_STRUCTURE_HEADER_RE = re.compile(
    r"^structure[ \t]+[A-Za-z_][A-Za-z0-9_.']*[^\n]*\bwhere[ \t]*$",
    re.MULTILINE,
)
_LEAN_TOP_LEVEL_DECL_RE = re.compile(
    r"^(?:abbrev|class|def|end|inductive|lemma|namespace|structure|theorem)\b",
    re.MULTILINE,
)
# Directories pruned wholesale from the axiom scan — these mirror
# `sorry_analyzer.py`'s _NEVER_DESCEND plus the dep cache.
_AXIOM_SKIP_DIRS = {".archon", ".git", ".lake", "lake-packages"}


def _strip_tex_comments(text: str) -> str:
    """Strip LaTeX line comments from ``text``.

    A ``%`` begins a comment to end-of-line, UNLESS escaped as ``\\%``.
    LaTeX commenting also drops the trailing newline when the entire
    remainder of the line is a comment, but we keep the newline since
    we only care about which macros appear, not the rendered output.
    """
    out_lines: list[str] = []
    for line in text.splitlines():
        i = 0
        n = len(line)
        result_chars: list[str] = []
        while i < n:
            ch = line[i]
            if ch == "\\" and i + 1 < n:
                # Escaped char: copy both, never a comment starter.
                result_chars.append(ch)
                result_chars.append(line[i + 1])
                i += 2
                continue
            if ch == "%":
                # Rest of line is a comment.
                break
            result_chars.append(ch)
            i += 1
        out_lines.append("".join(result_chars))
    return "\n".join(out_lines)
# References that point at an existing label. ``\uses{a, b}`` may list
# multiple labels separated by commas; we split on commas and trim.
# All inner classes use ``*?`` (not ``+?``) so empty ``\ref{}`` /
# ``\uses{}`` etc. match and are routed to ``malformed_refs`` rather
# than silently dropped. Non-empty matches feed the broken-ref check
# unchanged.
_REF_RES = (
    re.compile(r"\\ref\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\eqref\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\cref\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\Cref\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\autoref\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\uses\s*\{\s*([^{}]*?)\s*\}"),
    re.compile(r"\\proves\s*\{\s*([^{}]*?)\s*\}"),
)

# A literal standalone "REF" token in prose ("Definition~REF",
# "Sections REF–REF") — a writer pasted a placeholder instead of a
# resolvable \cref{<label>}. Matched with the optional preceding
# kind-word so the finding reads naturally.
_LITERAL_REF_RE = re.compile(
    r"(?:\b(?:Definition|Lemma|Theorem|Proposition|Corollary|Chapter|"
    r"Section|Remark|Equation|Step|Part)s?[~\s]+)?"
    r"(?<![A-Za-z\\{:_])REF(?![A-Za-z}_:])"
)

# A bare label-like token in prose ("Thm.~th:main", "Cor.~cor:algsch") — a
# writer pasted a LaTeX label id instead of the human theorem number or a
# \cref{}. Only matched OUTSIDE braces (annotation arguments are stripped
# before the scan).
_BARE_LABEL_RE = re.compile(
    r"(?<![\\{:\w])(?:thm?|lemma|lem|lm|cor|defn?|prop|sec|chap|eqn?|rem|rmk)"
    r":[A-Za-z][A-Za-z0-9_-]+"
)
# Strip every {...} argument so labels inside \uses{}/\cref{}/\label{} (and
# any other command argument) never reach the bare-label scan.
_BRACE_ARG_RE = re.compile(r"\{[^{}]*\}")


def _scan_math_delims(text: str) -> list[tuple[int, str]]:
    """Detect interleaved/unbalanced math delimiters: ``$ … \\( … \\) … $``.

    Balanced *counts* don't catch the real failure mode (a writer switching
    delimiter style mid-formula), so this walks the file with a tiny mode
    machine. Returns ``(line_number, problem)`` pairs.
    """
    probs: list[tuple[int, str]] = []
    mode: str | None = None  # None | '$' | '$$' | 'paren'
    line = 1
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1; i += 1; continue
        if c == "\\":
            nxt = text[i + 1: i + 2]
            if nxt == "(":
                if mode in ("$", "$$"):
                    probs.append((line, f"\\( opened inside {mode}…{mode} math"))
                elif mode == "paren":
                    probs.append((line, "nested \\( inside \\(…\\)"))
                else:
                    mode = "paren"
                i += 2; continue
            if nxt == ")":
                if mode == "paren":
                    mode = None
                else:
                    probs.append((line, "\\) without a matching \\("))
                i += 2; continue
            i += 2; continue  # skip escaped char (\$, \\, …)
        if c == "$":
            if text[i + 1: i + 2] == "$":
                if mode is None:
                    mode = "$$"
                elif mode == "$$":
                    mode = None
                else:
                    probs.append((line, f"$$ inside {mode} math"))
                i += 2; continue
            if mode is None:
                mode = "$"
            elif mode == "$":
                mode = None
            else:
                probs.append((line, "$ inside \\(…\\) math"))
            i += 1; continue
        i += 1
    if mode is not None:
        probs.append((line, f"unclosed {mode} math at end of file"))
    return probs


@dataclass
class DoctorReport:
    """Aggregate findings the loop summarizes + the phase commits."""
    chapters_dir: Path
    content_tex: Path
    chapters_present: list[Path] = field(default_factory=list)
    chapters_included: list[Path] = field(default_factory=list)
    orphan_chapters: list[Path] = field(default_factory=list)
    labels_defined: set[str] = field(default_factory=set)
    broken_refs: list[tuple[Path, str, str]] = field(default_factory=list)
    # (referencing_chapter, ref_kind, missing_label)
    malformed_refs: list[tuple[Path, str, str]] = field(default_factory=list)
    # (file, ref_kind, reason) — empty-argument annotations
    # (\uses{}/\proves{}/\label{}/\ref{}/...) and empty list items
    # (\uses{a,,b}). Reason is a short human-readable phrase such as
    # "empty argument" or "empty list item".
    axiom_decls: list[tuple[Path, str]] = field(default_factory=list)
    # (lean_file, decl_name) — every `axiom` found under project .lean
    covers_problems: list[tuple[str, str]] = field(default_factory=list)
    # (kind, detail) — `% archon:covers` integrity issues: a covered file
    # that doesn't exist, or a file claimed by more than one chapter.
    physics_modeling_problems: list[tuple[Path, str, str]] = field(default_factory=list)
    # (lean_file, kind, reason) — physics-aware projects must not silently
    # collapse quantities to bare Real/ℝ or leave key contract relations
    # underdetermined.
    physics_grounding_problems: list[tuple[Path, str, str]] = field(default_factory=list)
    # (lean_file, kind, reason) — physics-aware Lean targets must leave a
    # task_results report with LeanExplore/PhysLean grounding evidence.

    @property
    def has_findings(self) -> bool:
        return (
            bool(self.orphan_chapters)
            or bool(self.broken_refs)
            or bool(self.malformed_refs)
            or bool(self.axiom_decls)
            or bool(self.covers_problems)
            or bool(self.physics_modeling_problems)
            or bool(self.physics_grounding_problems)
        )

    def as_dict(self) -> dict:
        return {
            "chapters_dir": str(self.chapters_dir),
            "content_tex": str(self.content_tex),
            "chapters_present": [str(p) for p in sorted(self.chapters_present)],
            "chapters_included": [str(p) for p in sorted(self.chapters_included)],
            "orphan_chapters": [str(p) for p in sorted(self.orphan_chapters)],
            "labels_defined_count": len(self.labels_defined),
            "broken_refs": [
                {"chapter": str(c), "kind": k, "label": lbl}
                for c, k, lbl in sorted(self.broken_refs, key=lambda t: (str(t[0]), t[1], t[2]))
            ],
            "malformed_refs": [
                {"chapter": str(c), "kind": k, "reason": r}
                for c, k, r in sorted(self.malformed_refs, key=lambda t: (str(t[0]), t[1], t[2]))
            ],
            "axiom_decls": [
                {"file": str(f), "name": n}
                for f, n in sorted(self.axiom_decls, key=lambda t: (str(t[0]), t[1]))
            ],
            "covers_problems": [
                {"kind": k, "detail": d}
                for k, d in sorted(self.covers_problems)
            ],
            "physics_modeling_problems": [
                {"file": str(f), "kind": k, "reason": r}
                for f, k, r in sorted(
                    self.physics_modeling_problems,
                    key=lambda t: (str(t[0]), t[1], t[2]),
                )
            ],
            "physics_grounding_problems": [
                {"file": str(f), "kind": k, "reason": r}
                for f, k, r in sorted(
                    self.physics_grounding_problems,
                    key=lambda t: (str(t[0]), t[1], t[2]),
                )
            ],
        }


def _resolve_input_target(arg: str, src_dir: Path) -> Path | None:
    """Resolve a ``\\input{...}`` / ``\\include{...}`` argument to a Path.

    LaTeX accepts the argument with or without the ``.tex`` extension and
    interprets it relative to the document's source dir. Returns the
    resolved Path if it points at a file under ``src_dir`` that exists,
    otherwise None.
    """
    arg = arg.strip()
    if not arg:
        return None
    candidate = src_dir / arg
    if candidate.suffix != ".tex":
        candidate = candidate.with_suffix(".tex")
    if candidate.is_file():
        return candidate.resolve()
    # Some authors write ``\input{chapters/Foo}`` — already handled by the
    # relative-to-src_dir construction. Also support absolute-ish refs.
    return None


def _collect_inputs(start: Path, src_dir: Path) -> set[Path]:
    """Walk ``\\input`` / ``\\include`` from ``start`` recursively.

    Returns the set of resolved ``.tex`` files reachable from ``start``
    (including ``start`` itself when it exists). Cycles are tolerated by
    the visited-set.
    """
    visited: set[Path] = set()
    stack: list[Path] = [start.resolve()] if start.is_file() else []
    while stack:
        path = stack.pop()
        if path in visited:
            continue
        visited.add(path)
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        text = _strip_tex_comments(text)
        for m in _INPUT_RE.finditer(text):
            resolved = _resolve_input_target(m.group(1), src_dir)
            if resolved is not None and resolved not in visited:
                stack.append(resolved)
    return visited


def _scan_labels_and_refs(
    tex_files: list[Path],
) -> tuple[set[str], list[tuple[Path, str, str]], list[tuple[Path, str, str]]]:
    """Return (defined-labels, raw-references, malformed) across the .tex files.

    * ``defined-labels``: every non-empty ``\\label{X}`` target. Used by
      the caller to filter ``raw-references`` into broken vs resolved.
    * ``raw-references``: ``(file, ref_kind, label)`` for every non-empty
      ``\\ref{...}`` / ``\\uses{...}`` / etc. ``\\uses{a, b}`` produces
      one entry per comma-separated label.
    * ``malformed``: ``(file, ref_kind, reason)`` for every empty
      annotation (``\\uses{}``, ``\\label{}``, ``\\ref{}``, ...) and
      every empty list item inside an otherwise-non-empty
      ``\\uses{a,,b}``. These never reach plastex as resolvable labels
      and crash its depgraph build; surfacing them here lets the
      reviewer fix them before the next ``leanblueprint web``.
    """
    labels: set[str] = set()
    refs: list[tuple[Path, str, str]] = []
    malformed: list[tuple[Path, str, str]] = []
    for tex in tex_files:
        try:
            text = tex.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        text = _strip_tex_comments(text)
        # Literal "REF" placeholders — a writer wrote prose like
        # "Definition~REF" instead of a resolvable \cref{<label>}. plasTeX
        # renders them as-is, littering the blueprint with dead references.
        for m in _LITERAL_REF_RE.finditer(text):
            malformed.append((
                tex, "literal-ref",
                f'literal "{m.group(0)}" placeholder — use \\cref{{<label>}}',
            ))
        # Interleaved/unbalanced math delimiters ($ … \( … \) … $) — these
        # shred the rendered output mid-formula in both plasTeX and the
        # dashboard. Capped so one badly damaged file doesn't flood the report.
        for line_no, prob in _scan_math_delims(text)[:8]:
            malformed.append((tex, "math-delim", f"line {line_no}: {prob}"))
        # Bare label ids in prose ("Thm.~th:main") — outside any {...}.
        for m in _BARE_LABEL_RE.finditer(_BRACE_ARG_RE.sub(" ", text)):
            malformed.append((
                tex, "bare-label",
                f'bare label "{m.group(0)}" in prose — use \\cref{{{m.group(0)}}} '
                f"or the human-readable number",
            ))
        for m in _LABEL_RE.finditer(text):
            piece = m.group(1).strip()
            if piece:
                labels.add(piece)
            else:
                malformed.append((tex, "label", "empty argument"))
        for ref_re in _REF_RES:
            kind = ref_re.pattern.split("\\\\")[1].split("\\")[0]
            kind = re.match(r"[A-Za-z]+", kind).group(0)  # type: ignore[union-attr]
            for m in ref_re.finditer(text):
                arg = m.group(1).strip()
                if not arg:
                    # \uses{} / \ref{} / etc. — empty body.
                    malformed.append((tex, kind, "empty argument"))
                    continue
                # \uses{a, b, c} → ["a", "b", "c"]; empty pieces from
                # `\uses{a,,b}` or `\uses{a,}` are also malformed.
                for piece in arg.split(","):
                    piece = piece.strip()
                    if piece:
                        refs.append((tex, kind, piece))
                    else:
                        malformed.append((tex, kind, "empty list item"))
    return labels, refs, malformed


# ── Undefined-macro lint ──────────────────────────────────────────────────────
# A chapter using a control sequence that is neither defined in the project
# (macros/*.tex or a chapter-local \newcommand/\providecommand/
# \DeclareMathOperator/\def) nor a standard TeX/LaTeX/KaTeX command renders
# as raw TeX in both the dashboard and the compiled blueprint. The whitelist
# is deliberately generous — a missed exotic-but-valid command costs one
# advisory finding; a missed undefined macro costs unreadable output.

_MACRO_DEF_RES = (
    re.compile(r"\\(?:re)?newcommand\*?\s*\{?\\([A-Za-z@]+)\}?"),
    re.compile(r"\\providecommand\*?\s*\{?\\([A-Za-z@]+)\}?"),
    re.compile(r"\\DeclareMathOperator\*?\s*\{\\([A-Za-z@]+)\}"),
    re.compile(r"\\def\s*\\([A-Za-z@]+)"),
    re.compile(r"\\DeclarePairedDelimiter\s*\{?\\([A-Za-z@]+)\}?"),
)
_USED_CMD_RE = re.compile(r"\\([A-Za-z]+)")

_KNOWN_TEX_COMMANDS: frozenset[str] = frozenset("""
alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa
varkappa lambda mu nu xi pi varpi rho varrho sigma varsigma tau upsilon phi
varphi chi psi omega digamma Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi
Psi Omega
frac dfrac tfrac cfrac sqrt binom dbinom tbinom genfrac atop over choose
sum prod coprod int oint iint iiint iiiint idotsint smallint
lim limsup liminf varinjlim varprojlim injlim projlim colim
sup inf min max log ln lg exp sin cos tan cot sec csc arcsin arccos arctan
sinh cosh tanh coth deg det dim gcd hom ker arg Pr mod pmod bmod
mathbb mathbf mathcal mathfrak mathrm mathsf mathtt mathit mathscr mathnormal
text textbf textit textrm textsf texttt textsc textup textnormal textmd
emph textsl underline bm boldsymbol operatorname mathop mathbin mathrel
mathord mathopen mathclose mathpunct mathstrut
hat widehat bar overline tilde widetilde vec dot ddot dddot breve check grave
acute mathring overbrace underbrace overrightarrow overleftarrow
overleftrightarrow underrightarrow underleftarrow xrightarrow xleftarrow
xmapsto overset underset stackrel substack
to mapsto rightarrow leftarrow Rightarrow Leftarrow leftrightarrow
Leftrightarrow longrightarrow longleftarrow Longrightarrow Longleftarrow
longmapsto longleftrightarrow Longleftrightarrow hookrightarrow hookleftarrow
twoheadrightarrow twoheadleftarrow rightharpoonup rightharpoondown
leftharpoonup leftharpoondown rightrightarrows leftleftarrows
rightleftarrows leftrightarrows rightleftharpoons uparrow downarrow
updownarrow Uparrow Downarrow Updownarrow nearrow searrow swarrow nwarrow
iff implies impliedby nleftarrow nrightarrow nLeftarrow nRightarrow
curvearrowright curvearrowleft circlearrowright circlearrowleft
rightsquigarrow leadsto dashrightarrow dashleftarrow
le leq ge geq ne neq sim simeq cong equiv approx propto prec succ preceq
succeq ll gg lll ggg subset supset subseteq supseteq subsetneq supsetneq
varsubsetneq sqsubset sqsupset sqsubseteq sqsupseteq nsubseteq nsupseteq
in ni notin mid nmid parallel nparallel perp vdash dashv nvdash models
vDash asymp doteq triangleq coloneqq eqqcolon coloneq colonequals doteqdot
between pitchfork smile frown lesssim gtrsim lessapprox gtrapprox lessgtr
gtrless trianglelefteq trianglerighteq vartriangleleft vartriangleright
pm mp times div cdot ast star circ bullet cap cup sqcap sqcup vee wedge
setminus smallsetminus oplus ominus otimes oslash odot bigcirc dagger
ddagger amalg uplus bigcup bigcap bigsqcup bigoplus bigotimes bigodot
bigvee bigwedge biguplus lhd rhd unlhd unrhd wr ltimes rtimes bowtie
circledast circledcirc circleddash boxplus boxminus boxtimes boxdot
infty partial nabla forall exists nexists emptyset varnothing angle
measuredangle sphericalangle triangle square Box Diamond lozenge aleph beth
gimel daleth hbar hslash ell wp Re Im imath jmath prime backprime backslash
top bot flat natural sharp clubsuit diamondsuit heartsuit spadesuit surd
checkmark maltese degree neg lnot complement
ldots cdots vdots ddots dots dotsb dotsc dotsm dotsi dotso
left right middle big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr Biggl
Biggr bigm Bigm langle rangle lceil rceil lfloor rfloor lvert rvert lVert
rVert vert Vert lbrace rbrace lbrack rbrack lgroup rgroup
quad qquad thinspace medspace thickspace negthinspace negmedspace
negthickspace enspace enskip hspace vspace hfill vfill phantom hphantom
vphantom smash mathllap mathrlap mathclap llap rlap clap kern mkern mskip
raisebox raise lower rule strut space
displaystyle textstyle scriptstyle scriptscriptstyle limits nolimits
displaylimits not cancel bcancel xcancel sout boxed tag notag nonumber
allowbreak relax protect ensuremath xspace
begin end label ref eqref pageref cref Cref autoref nameref vref item
caption chapter section subsection subsubsection paragraph subparagraph
part appendix footnote footnotemark footnotetext cite citep citet
bibliography bibliographystyle input include includeonly includegraphics
newcommand renewcommand providecommand DeclareMathOperator
DeclarePairedDelimiter newenvironment renewenvironment newtheorem
theoremstyle numberwithin setcounter addtocounter stepcounter value
documentclass usepackage RequirePackage ProvidesPackage title author date
maketitle tableofcontents listoffigures listoftables abstract and thanks
uses lean leanok mathlibok notready proves discussion home github dochome
color textcolor colorbox fbox framebox definecolor pagecolor
small tiny scriptsize footnotesize normalsize large Large LARGE huge Huge
itshape upshape slshape scshape bfseries mdseries rmfamily sffamily ttfamily
em it bf rm sf tt sl sc cal frak
centering raggedright raggedleft noindent indent par newline newpage
clearpage cleardoublepage linebreak nolinebreak pagebreak nopagebreak
bigskip medskip smallskip vskip hskip baselineskip parskip parindent
mbox makebox hbox vbox fboxsep fboxrule
S P copyright dag ddag pounds euro yen S P
v u c H r b d t k
if else fi ifmmode ifdim ifnum let expandafter csname endcsname
noexpand string detokenize empty today TeX LaTeX KaTeX
min max argmin argmax sgn sech csch arcsinh arccosh arctanh
colon textbackslash textasciitilde textasciicircum texorpdfstring href url
qed qedhere qedsymbol hline cline multicolumn multirow textsuperscript
textsubscript enquote roman Roman arabic alph Alph fnsymbol
triangleleft triangleright lor land bigtriangleup bigtriangledown
leftrightsquigarrow ar arrow matrix verb path
operatorname Hom End Aut Spec id
""".split())
# NOTE: `Hom`/`End`/`Aut`/`Spec`/`id` above are NOT TeX builtins — they are
# whitelisted because virtually every AG/CT blueprint defines them in
# macros/common.tex from day one; flagging them would be noise. Everything
# else project-specific must be defined to pass.


def _scan_undefined_macros(
    chapter_files: list[Path],
    def_sources: list[Path],
) -> list[tuple[Path, str, str]]:
    """Flag control sequences used in chapters but defined nowhere.

    ``def_sources`` is every .tex that may carry definitions (macros/*.tex,
    preamble files, and the chapters themselves for chapter-local
    ``\\providecommand``). One finding per (file, command).
    """
    defined: set[str] = set()
    for tex in def_sources:
        try:
            text = _strip_tex_comments(tex.read_text(encoding="utf-8", errors="ignore"))
        except OSError:
            continue
        for d_re in _MACRO_DEF_RES:
            defined.update(m.group(1) for m in d_re.finditer(text))

    out: list[tuple[Path, str, str]] = []
    for tex in chapter_files:
        try:
            text = _strip_tex_comments(tex.read_text(encoding="utf-8", errors="ignore"))
        except OSError:
            continue
        seen: set[str] = set()
        for m in _USED_CMD_RE.finditer(text):
            cmd = m.group(1)
            if cmd in seen or cmd in defined or cmd in _KNOWN_TEX_COMMANDS:
                continue
            seen.add(cmd)
            out.append((
                tex, "undefined-macro",
                f"\\{cmd} is used but defined nowhere (macros/*.tex or a "
                f"chapter-local \\providecommand) — define it or fix the typo",
            ))
    return out


def _scan_axiom_decls(project_path: Path) -> list[tuple[Path, str]]:
    """Find all ``axiom`` declarations under the project's .lean files.

    Skips the same directory set that ``sorry_analyzer.py`` excludes
    (``.archon`` / ``.git`` / ``.lake`` / ``lake-packages``). Comments
    are stripped before regex-matching to avoid false positives on
    docstrings or comment-out lines (`-- axiom foo : ...`).

    Returns ``[]`` when no axioms are present anywhere; the doctor
    surfaces axioms as a finding when this list is non-empty.
    """
    import os
    out: list[tuple[Path, str]] = []
    if not project_path.is_dir():
        return out
    for root, dirs, files in os.walk(project_path):
        dirs[:] = [d for d in dirs if d not in _AXIOM_SKIP_DIRS]
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            lean = Path(root) / filename
            try:
                text = lean.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            # Strip Lean line comments (``--`` to end-of-line) and
            # block comments (``/- ... -/``) before matching. The
            # regex doesn't anchor strictly enough to skip those
            # otherwise, and `-- axiom foo` inside a TODO would be a
            # false positive.
            stripped = _strip_lean_comments(text)
            for m in _AXIOM_RE.finditer(stripped):
                out.append((lean, m.group(1)))
    return out


def _strip_lean_comments(text: str) -> str:
    """Remove Lean ``--`` line comments and nested ``/- ... -/`` blocks.

    Conservative: when the parser can't decide (unterminated block, for
    example), errs on the side of keeping the original text. The
    output is used only as input to ``_AXIOM_RE`` so a slight over-
    keep is harmless — false positives still get the axiom name in the
    report, false negatives would silently miss real axioms.
    """
    result: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            # Preserve newlines so line-based regexes still anchor.
            if ch == "\n":
                result.append("\n")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth += 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            # Skip to end-of-line; keep the newline.
            while i < n and text[i] != "\n":
                i += 1
            continue
        result.append(ch)
        i += 1
    return "".join(result)


def _has_physics_blueprint_marker(chapter_files: list[Path]) -> bool:
    """Return true when any live blueprint chapter opts into physics checks."""
    for tex in chapter_files:
        try:
            if _PHYSICS_MARKER in tex.read_text(encoding="utf-8", errors="ignore"):
                return True
        except OSError:
            continue
    return False


def _looks_like_physical_quantity_name(name: str) -> bool:
    tail = name.rsplit(".", 1)[-1].lower()
    return any(part in tail for part in _PHYSICS_QUANTITY_NAME_PARTS)


def _identifier_occurrences(text: str, name: str) -> list[re.Match[str]]:
    pattern = re.compile(
        rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])"
    )
    return list(pattern.finditer(text))


def _used_only_in_existential_field(
    text: str,
    *,
    declaration_end: int,
    use_start: int,
) -> bool:
    field_headers = list(
        _PHYSICS_STRUCTURE_FIELD_RE.finditer(text, declaration_end, use_start)
    )
    if not field_headers:
        return False
    block_start = field_headers[-1].start()
    next_header = _PHYSICS_STRUCTURE_FIELD_RE.search(text, use_start + 1)
    block_end = next_header.start() if next_header else len(text)
    block = text[block_start:block_end]
    return "∃" in block or re.search(r"\bExists\b", block) is not None


def _scan_opaque_physics_relations(
    lean: Path,
    stripped: str,
) -> list[tuple[Path, str, str]]:
    """Flag existential-only load-bearing predicates with no eliminator law."""
    out: list[tuple[Path, str, str]] = []
    for declaration in _PHYSICS_PROP_FIELD_RE.finditer(stripped):
        name = declaration.group(1)
        lowered = name.lower()
        if not any(part in lowered for part in _PHYSICS_LOAD_BEARING_PREDICATE_PARTS):
            continue
        occurrences = _identifier_occurrences(stripped, name)
        if len(occurrences) != 2:
            continue
        use = occurrences[1]
        if not _used_only_in_existential_field(
            stripped,
            declaration_end=declaration.end(),
            use_start=use.start(),
        ):
            continue
        out.append((
            lean,
            "opaque-existential-physics-relation",
            f"{name} is a load-bearing Prop-valued relation used only inside "
            "an existential witness; add an equation, inequality, geometric "
            "condition, limit/derivative law, or reusable eliminator that "
            "connects it to the target.",
        ))
    return out


def _scan_unpropagated_uncertainty(
    lean: Path,
    stripped: str,
) -> list[tuple[Path, str, str]]:
    """Flag central-value error bands that omit a paired uncertainty field."""
    theorem_headers = [
        match.group(0) for match in _LEAN_THEOREM_HEADER_RE.finditer(stripped)
    ]
    out: list[tuple[Path, str, str]] = []
    for structure in _LEAN_STRUCTURE_HEADER_RE.finditer(stripped):
        next_declaration = _LEAN_TOP_LEVEL_DECL_RE.search(stripped, structure.end())
        block_end = next_declaration.start() if next_declaration else len(stripped)
        block = stripped[structure.end():block_end]
        real_fields = list(_PHYSICS_REAL_FIELD_RE.finditer(block))
        central_names = {
            match.group(1) for match in real_fields
            if "central" in match.group(1).lower()
        }
        if not central_names:
            continue
        for declaration in real_fields:
            name = declaration.group(1)
            lowered = name.lower()
            if "uncertainty" not in lowered and "error" not in lowered:
                continue
            # A definition/propagation law adds another occurrence. Three or
            # fewer means the field is typically only declared, constrained
            # nonnegative, and assigned by a previous-part result.
            if len(_identifier_occurrences(stripped, name)) > 3:
                continue
            for header in theorem_headers:
                has_error_band = re.search(
                    r"\|.*?\|[ \t\n]*≤", header, re.DOTALL
                )
                uses_central_value = any(
                    central in header for central in central_names
                )
                if has_error_band and uses_central_value and name not in header:
                    out.append((
                        lean,
                        "unpropagated-uncertainty",
                        f"{name} is modeled but absent from a theorem contract "
                        "that bounds its paired central-value error band; "
                        "propagate the uncertainty explicitly or justify why "
                        "it is not applicable.",
                    ))
                    break
    return out


def _scan_physics_modeling_problems(
    project_path: Path,
    *,
    enabled: bool,
) -> list[tuple[Path, str, str]]:
    """Flag conservative modeling/contract defects in physics projects."""
    if not enabled or not project_path.is_dir():
        return []

    import os
    out: list[tuple[Path, str, str]] = []
    for root, dirs, files in os.walk(project_path):
        dirs[:] = [d for d in dirs if d not in _AXIOM_SKIP_DIRS]
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            lean = Path(root) / filename
            try:
                text = lean.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            stripped = _strip_lean_comments(text)
            for kind, pattern, reason in _PHYSICS_SELF_CONTAINED_PATTERNS:
                if pattern.search(stripped) or (
                    kind == "self-contained-physics-file" and pattern.search(text)
                ):
                    out.append((lean, kind, reason))
            for m in _PHYSICS_SCALAR_FALLBACK_RE.finditer(stripped):
                decl_name = m.group(1)
                scalar = m.group(2)
                if not _looks_like_physical_quantity_name(decl_name):
                    continue
                out.append((
                    lean,
                    "scalar-fallback",
                    f"{decl_name} is defined directly as {scalar}; use a "
                    "typed physical model with explicit units/dimensions, "
                    "or document a named scalar projection in the blueprint.",
                ))
            out.extend(_scan_opaque_physics_relations(lean, stripped))
            out.extend(_scan_unpropagated_uncertainty(lean, stripped))
    return out


def _physics_chapter_targets(project_path: Path, chapter_files: list[Path]) -> list[Path]:
    """Return existing Lean files covered by live `% archon:physics` chapters."""
    try:
        from archon.commands.tooling.blueprint import parse_chapter_covers
    except Exception:
        parse_chapter_covers = None

    targets: set[Path] = set()
    for tex in chapter_files:
        try:
            text = tex.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if _PHYSICS_MARKER not in text:
            continue

        covers: list[str] = []
        if parse_chapter_covers is not None:
            try:
                covers = parse_chapter_covers(text)
            except Exception:
                covers = []
        if not covers:
            covers = [f"{tex.stem}.lean"]

        for rel in covers:
            rel_path = Path(rel)
            if rel_path.is_absolute():
                candidate = rel_path
            else:
                candidate = project_path / rel_path
            if candidate.is_file() and candidate.suffix == ".lean":
                targets.add(candidate.resolve())
    return sorted(targets)


def _scan_physics_target_import_problems(
    project_path: Path,
    chapter_files: list[Path],
    *,
    enabled: bool,
) -> list[tuple[Path, str, str]]:
    """Require physics Lean targets to visibly use the real Lean libraries."""
    if not enabled:
        return []

    out: list[tuple[Path, str, str]] = []
    for lean_file in _physics_chapter_targets(project_path, chapter_files):
        try:
            text = lean_file.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        imports = _LEAN_IMPORT_RE.findall(text)
        has_mathlib = any(pkg == "Mathlib" or pkg.startswith("Mathlib.") for pkg in imports)
        has_physlib = any(
            pkg == "Physlib"
            or pkg.startswith("Physlib.")
            or pkg == "PhysLean"
            or pkg.startswith("PhysLean.")
            for pkg in imports
        )
        if not has_mathlib:
            out.append((
                lean_file,
                "missing-mathlib-import",
                "physics target does not import Mathlib; autoformalization "
                "must be checked in a real Lake/Mathlib environment, not as "
                "a standalone Lean smoke file",
            ))
        if not has_physlib:
            out.append((
                lean_file,
                "missing-physlib-import",
                "physics target does not import Physlib/PhysLean; attempted "
                "grounding should use the available formal physics library "
                "before introducing local abstractions",
            ))
    return out


def _candidate_grounding_reports(project_path: Path, lean_file: Path) -> list[Path]:
    """Return likely task_results reports for one Lean target."""
    state_dir = project_path / ".archon"
    task_results = state_dir / "task_results"
    if not task_results.is_dir():
        return []
    try:
        rel = lean_file.resolve().relative_to(project_path.resolve())
    except ValueError:
        rel = Path(lean_file.name)
    rel_posix = rel.as_posix()
    slug = rel_posix.replace("/", "_")
    no_suffix = rel.with_suffix("").as_posix()
    no_suffix_slug = no_suffix.replace("/", "_")

    names = [
        f"{rel_posix}.md",
        f"{no_suffix}.md",
        f"{rel.name}.md",
        f"{rel.stem}.md",
        f"{slug}.md",
        f"{no_suffix_slug}.md",
    ]
    out: list[Path] = []
    seen: set[Path] = set()
    for name in names:
        p = task_results / name
        if p.is_file() and p not in seen:
            out.append(p)
            seen.add(p)

    # Some agent-generated reports include extra slug text. Accept fuzzy
    # matches only when the report file itself looks like a physics/formalize/
    # prover report; generic blueprint-reviewer reports often mention the Lean
    # target, but they are not grounding logs.
    stem_key = rel.stem.lower().replace("_", "-")
    for p in sorted(task_results.rglob("*.md")):
        if p in seen:
            continue
        p_key = p.stem.lower().replace("_", "-")
        if (
            not p_key.startswith(stem_key)
            and "physics" not in p_key
            and "formalize" not in p_key
            and "prover" not in p_key
        ):
            continue
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if rel_posix in text or rel.name in text:
            out.append(p)
            seen.add(p)
    return out


def _grounding_report_missing_terms(text: str) -> list[str]:
    hay = text.lower()
    missing: list[str] = []
    for label, terms in _PHYSICS_GROUNDING_REQUIRED_TERMS:
        if not any(term in hay for term in terms):
            missing.append(label)
    if "mathlib" not in hay:
        missing.append("Mathlib package")
    if "physlean" not in hay and "physlib" not in hay:
        missing.append("PhysLean package")
    if (
        "grounding status: incomplete" in hay
        or "leanexplore_api_key is missing" in hay
        or "error:" in hay
    ):
        missing.append("successful LeanExplore search")
    return missing


def _scan_physics_grounding_problems(
    project_path: Path,
    chapter_files: list[Path],
    *,
    enabled: bool,
) -> list[tuple[Path, str, str]]:
    """Flag missing/incomplete LeanExplore grounding logs for physics targets."""
    if not enabled:
        return []

    out: list[tuple[Path, str, str]] = []
    for lean_file in _physics_chapter_targets(project_path, chapter_files):
        reports = _candidate_grounding_reports(project_path, lean_file)
        try:
            rel = lean_file.relative_to(project_path.resolve()).as_posix()
        except ValueError:
            rel = str(lean_file)
        if not reports:
            out.append((
                lean_file,
                "missing-grounding-log",
                f"{rel} exists under a `% archon:physics` chapter, but no "
                "task_results report records LeanExplore grounding. The "
                "autoformalize/prover report must list LeanExplore queries, "
                "candidates, grounded Mathlib/PhysLean names, local "
                "abstractions, and grounding gaps.",
            ))
            continue

        best_missing: list[str] | None = None
        best_report: Path | None = None
        for report in reports:
            try:
                text = report.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            missing = _grounding_report_missing_terms(text)
            if not missing:
                best_missing = []
                best_report = report
                break
            if best_missing is None or len(missing) < len(best_missing):
                best_missing = missing
                best_report = report
        if best_missing:
            report_label = best_report.as_posix() if best_report else "<unreadable>"
            out.append((
                lean_file,
                "incomplete-grounding-log",
                f"{rel} has a task_results report at {report_label}, but its "
                "LeanExplore grounding evidence is incomplete; missing: "
                + ", ".join(best_missing)
                + ".",
            ))
    return out


def _scan_covers_problems(project_path: Path) -> list[tuple[str, str]]:
    """Integrity check for ``% archon:covers`` declarations.

    Flags (a) a covers entry naming a Lean file that doesn't exist, and
    (b) a Lean file claimed by more than one chapter. Both are silent
    mis-mappings that would make the prover-dispatch gate consult the
    wrong chapter (or two), so they're worth surfacing deterministically.
    """
    from archon.commands.tooling.blueprint import chapter_coverage_map

    coverage = chapter_coverage_map(project_path)
    problems: list[tuple[str, str]] = []
    for slug, files in sorted(coverage.items()):
        for f in files:
            if not (project_path / f).is_file():
                problems.append((
                    "missing_file",
                    f"chapter `{slug}.tex` covers `{f}`, which does not exist",
                ))
    owners: dict[str, list[str]] = {}
    for slug, files in coverage.items():
        for f in files:
            owners.setdefault(f, []).append(slug)
    for f, slugs in sorted(owners.items()):
        if len(slugs) > 1:
            problems.append((
                "double_coverage",
                f"`{f}` is covered by multiple chapters: "
                + ", ".join(f"`{s}.tex`" for s in sorted(slugs)),
            ))
    return problems


def run_blueprint_doctor(project_path: Path) -> DoctorReport | None:
    """Run the blueprint doctor on ``project_path``.

    Returns ``None`` when the project has no blueprint to lint (no
    ``blueprint/src/`` directory) — the caller treats that as a silent
    skip. Returns a ``DoctorReport`` otherwise, possibly empty.

    The axiom scan runs regardless of blueprint presence: even a
    blueprint-less project benefits from "no new axioms" enforcement.
    A project with neither a blueprint nor any ``.lean`` files
    short-circuits to ``None``.
    """
    src_dir = (project_path / "blueprint" / "src").resolve()
    chapters_dir = (src_dir / "chapters").resolve()
    content_tex = src_dir / "content.tex"

    has_blueprint = src_dir.is_dir()

    chapters_present = sorted(p.resolve() for p in chapters_dir.glob("*.tex")) \
        if chapters_dir.is_dir() else []

    included = _collect_inputs(content_tex, src_dir) if has_blueprint else set()
    # Restrict the "included chapters" set to files under chapters_dir.
    chapters_included = sorted(
        p for p in included
        if chapters_dir in p.parents
    )
    chapters_included_set = set(chapters_included)
    orphan_chapters = sorted(
        p for p in chapters_present if p not in chapters_included_set
    )

    # For label/ref scanning, take the union of every transitively-included
    # .tex (which includes content.tex itself + any preamble files it
    # \inputs). This way \label{X} defined in a sub-included file is
    # available for cross-references in another chapter.
    label_scan_targets = sorted(included)
    labels, refs, malformed = _scan_labels_and_refs(label_scan_targets)

    # Undefined macros: definitions may live in macros/*.tex (whether or not
    # content.tex \inputs them — web.tex usually does), any included file, or
    # the chapter itself; usage is only linted inside chapters.
    if has_blueprint:
        macros_dir = src_dir / "macros"
        def_sources = sorted({
            *included,
            *chapters_present,
            *(macros_dir.glob("*.tex") if macros_dir.is_dir() else ()),
        })
        malformed += _scan_undefined_macros(
            chapters_included or chapters_present, def_sources,
        )

    broken: list[tuple[Path, str, str]] = []
    for tex, kind, lbl in refs:
        if lbl not in labels:
            broken.append((tex, kind, lbl))

    axiom_decls = _scan_axiom_decls(project_path)
    covers_problems = _scan_covers_problems(project_path) if has_blueprint else []
    physics_enabled = (
        _has_physics_blueprint_marker(chapters_included or chapters_present)
        if has_blueprint else False
    )
    physics_modeling_problems = _scan_physics_modeling_problems(
        project_path,
        enabled=physics_enabled,
    )
    physics_modeling_problems.extend(
        _scan_physics_target_import_problems(
            project_path,
            chapters_included or chapters_present,
            enabled=physics_enabled,
        )
    )
    physics_grounding_problems = _scan_physics_grounding_problems(
        project_path,
        chapters_included or chapters_present,
        enabled=physics_enabled,
    )

    if (
        not has_blueprint
        and not axiom_decls
        and not physics_modeling_problems
        and not physics_grounding_problems
    ):
        # Pure-Lean project with no blueprint AND no axioms — nothing
        # for the doctor to do. Skip so callers don't get an empty
        # report cluttering logs/iter-NNN/.
        return None

    return DoctorReport(
        chapters_dir=chapters_dir,
        content_tex=content_tex,
        chapters_present=chapters_present,
        chapters_included=chapters_included,
        orphan_chapters=orphan_chapters,
        labels_defined=labels,
        broken_refs=broken,
        malformed_refs=malformed,
        axiom_decls=axiom_decls,
        covers_problems=covers_problems,
        physics_modeling_problems=physics_modeling_problems,
        physics_grounding_problems=physics_grounding_problems,
    )


def blueprint_doctor_cli(
    project_path: str = typer.Option(".", "--project-path", help="Path to Lean project"),
    as_json: bool = typer.Option(False, "--json", help="Emit JSON instead of text."),
) -> None:
    """Lint the blueprint: orphan chapters, broken/malformed references,
    literal-REF placeholders, interleaved math delimiters, bare labels in
    prose, undefined macros, axioms, and `% archon:covers` problems.

    The same checks the loop and `archon dag` run between phases — exposed
    on demand so review agents (and you) can re-lint after editing chapters.
    """
    import json as _json
    root = Path(project_path).resolve()
    report = run_blueprint_doctor(root)
    if report is None:
        print("{}" if as_json else "No blueprint (and no axioms) to lint.")
        return
    if as_json:
        print(_json.dumps(report.as_dict(), ensure_ascii=False))
        return

    def _rel(p: Path) -> str:
        try:
            return str(p.relative_to(root))
        except ValueError:
            return str(p)

    if not report.has_findings:
        print("blueprint-doctor: clean — no structural or rendering findings.")
        return
    from collections import Counter
    kinds = Counter(k for _, k, _ in report.malformed_refs)
    print(
        f"blueprint-doctor: {len(report.orphan_chapters)} orphan chapter(s), "
        f"{len(report.broken_refs)} broken ref(s), "
        f"{len(report.malformed_refs)} malformed "
        f"({', '.join(f'{k}: {n}' for k, n in sorted(kinds.items()))}), "
        f"{len(report.axiom_decls)} axiom(s), "
        f"{len(report.covers_problems)} covers problem(s), "
        f"{len(report.physics_modeling_problems)} physics modeling problem(s), "
        f"{len(report.physics_grounding_problems)} physics grounding problem(s)."
    )
    for p in report.orphan_chapters:
        print(f"- [orphan] {_rel(p)}")
    for tex, kind, lbl in report.broken_refs:
        print(f"- [broken {kind}] {_rel(tex)}: {lbl}")
    for tex, kind, reason in report.malformed_refs:
        print(f"- [{kind}] {_rel(tex)}: {reason}")
    for f, n in report.axiom_decls:
        print(f"- [axiom] {_rel(f)} :: {n}")
    for _kind, detail in report.covers_problems:
        print(f"- [covers] {detail}")
    for f, kind, reason in report.physics_modeling_problems:
        print(f"- [physics {kind}] {_rel(f)}: {reason}")
    for f, kind, reason in report.physics_grounding_problems:
        print(f"- [physics {kind}] {_rel(f)}: {reason}")


def write_reports(
    report: DoctorReport,
    iter_log_dir: Path,
    project_path: Path,
) -> tuple[Path, Path]:
    """Persist the doctor's findings as JSON + Markdown under iter-NNN/.

    Returns (json_path, markdown_path).
    """
    iter_log_dir.mkdir(parents=True, exist_ok=True)
    json_path = iter_log_dir / "blueprint-doctor.json"
    md_path = iter_log_dir / "blueprint-doctor.md"

    json_path.write_text(
        json.dumps(report.as_dict(), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    def _rel(p: Path) -> str:
        try:
            return str(p.relative_to(project_path.resolve()))
        except ValueError:
            return str(p)

    lines: list[str] = ["# Blueprint Doctor", ""]
    if not report.has_findings:
        lines.append(
            "No structural findings: every chapter is `\\input`'d by "
            "`content.tex`, every `\\ref{...}` / `\\uses{...}` resolves to "
            "a defined `\\label{...}`, every annotation has a non-empty "
            "argument, and no `axiom` declarations are present under the "
            "project's `.lean` files."
        )
        md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return json_path, md_path

    if report.axiom_decls:
        lines.append("## Axiom declarations")
        lines.append("")
        lines.append(
            "Archon's stance is **no new axioms**. The declarations below "
            "appear as `axiom <name> : ...` under the project's `.lean` "
            "files. Resolve each one before the next iter — either remove "
            "the axiom (and supply a real proof), or, if the axiom is the "
            "mathematician's explicit boundary marker, mark it protected "
            "in `archon-protected.yaml` and document the rationale."
        )
        lines.append("")
        for f, n in sorted(report.axiom_decls, key=lambda t: (str(t[0]), t[1])):
            lines.append(f"- `{_rel(f)}` :: `{n}`")
        lines.append("")

    if report.covers_problems:
        lines.append("## Chapter coverage problems (`% archon:covers`)")
        lines.append("")
        lines.append(
            "A chapter's `% archon:covers <file> ...` declaration tells the "
            "prover-dispatch gate which Lean files that chapter blueprints. "
            "The issues below would route the gate to the wrong chapter — "
            "fix the declaration (correct the path, or make exactly one "
            "chapter own each file)."
        )
        lines.append("")
        for _kind, detail in sorted(report.covers_problems):
            lines.append(f"- {detail}")
        lines.append("")

    if report.physics_modeling_problems:
        lines.append("## Physics modeling")
        lines.append("")
        lines.append(
            "Physics-aware chapters marked `% archon:physics` should preserve "
            "the meaning of load-bearing physical quantities. The Lean "
            "targets below either miss the real Mathlib/Physlib import path "
            "or introduce self-contained placeholder physics such as local "
            "scalar classes, tag-only dimensions, symbolic Taylor/asymptotic "
            "enums, fake Jacobian records, or bare `Real`/`ℝ` quantity "
            "collapses. Replace them with Mathlib/Physlib-grounded statements "
            "or a justified typed local model documented in the blueprint."
        )
        lines.append("")
        for f, kind, reason in sorted(
            report.physics_modeling_problems,
            key=lambda t: (str(t[0]), t[1], t[2]),
        ):
            lines.append(f"- `{_rel(f)}` :: `{kind}` - {reason}")
        lines.append("")

    if report.physics_grounding_problems:
        lines.append("## Physics grounding")
        lines.append("")
        lines.append(
            "Physics-aware autoformalization/proving must leave reviewable "
            "LeanExplore evidence in `.archon/task_results`. For each existing "
            "Lean target covered by a `% archon:physics` chapter, the report "
            "should list LeanExplore queries/candidates, grounded Mathlib/"
            "PhysLean names, local abstractions, and grounding gaps. Missing "
            "or incomplete logs mean the reviewer cannot tell whether the "
            "formalization was grounded or invented."
        )
        lines.append("")
        for f, kind, reason in sorted(
            report.physics_grounding_problems,
            key=lambda t: (str(t[0]), t[1], t[2]),
        ):
            lines.append(f"- `{_rel(f)}` :: `{kind}` - {reason}")
        lines.append("")

    if report.orphan_chapters:
        lines.append("## Orphan chapters")
        lines.append("")
        lines.append(
            "These `.tex` files exist under `blueprint/src/chapters/` "
            "but are NOT reachable from `content.tex` via `\\input` "
            "(directly or transitively). They contribute nothing to the "
            "rendered blueprint and likely indicate either a forgotten "
            "`\\input{...}` line in `content.tex` or stale chapter "
            "files left behind by a refactor."
        )
        lines.append("")
        for p in report.orphan_chapters:
            lines.append(f"- `{_rel(p)}`")
        lines.append("")

    if report.malformed_refs:
        lines.append("## Malformed annotations")
        lines.append("")
        lines.append(
            "Annotations with an empty argument (`\\uses{}`, `\\proves{}`, "
            "`\\label{}`, `\\ref{}`, ...) or an empty list item "
            "(`\\uses{a,,b}`, `\\uses{a,}`). plastex emits "
            "`Label '' could not be resolved` for each of these and then "
            "the leanblueprint depgraph builder enters infinite recursion "
            "(`RecursionError`), so the blueprint never finishes building. "
            "Fix each one by either filling in the intended label or "
            "deleting the empty annotation. Do NOT defer — the next "
            "`leanblueprint web` run will crash until these are resolved."
        )
        lines.append("")
        # Group by (chapter, kind, reason) for readability.
        by_chapter_m: dict[Path, dict[tuple[str, str], int]] = {}
        for chapter, kind, reason in report.malformed_refs:
            by_chapter_m.setdefault(chapter, {}).setdefault((kind, reason), 0)
            by_chapter_m[chapter][(kind, reason)] += 1
        for chapter in sorted(by_chapter_m):
            lines.append(f"### `{_rel(chapter)}`")
            for (kind, reason), count in sorted(by_chapter_m[chapter].items()):
                suffix = f" ×{count}" if count > 1 else ""
                lines.append(f"- `\\{kind}{{...}}` — {reason}{suffix}")
            lines.append("")

    if report.broken_refs:
        lines.append("## Broken cross-references")
        lines.append("")
        lines.append(
            "These `\\ref{...}` / `\\uses{...}` / `\\cref{...}` (etc.) "
            "calls point at labels that no `\\label{...}` defines anywhere "
            "in the included tex tree. The dependency graph rendered by "
            "leanblueprint will draw a missing edge for each. Common causes: "
            "label typos (case mismatch, plural/singular), labels moved to "
            "an orphan chapter, or copy-paste of `\\uses{...}` lists that "
            "weren't updated when targets renamed."
        )
        lines.append("")
        # Group by (chapter, kind) for readability.
        by_chapter: dict[Path, dict[str, list[str]]] = {}
        for chapter, kind, label in report.broken_refs:
            by_chapter.setdefault(chapter, {}).setdefault(kind, []).append(label)
        for chapter in sorted(by_chapter):
            lines.append(f"### `{_rel(chapter)}`")
            for kind in sorted(by_chapter[chapter]):
                for label in sorted(set(by_chapter[chapter][kind])):
                    lines.append(f"- `\\{kind}{{{label}}}` — no matching `\\label`")
            lines.append("")

    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return json_path, md_path
