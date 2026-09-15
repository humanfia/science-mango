"""Recognize only permutation differences in generated accepted Lean modules."""
import re


def _parts(text: str):
    chunks = re.split(r"(?m)^(?=theorem )", text)
    header = chunks[0]
    imports = []
    for line in header.splitlines():
        if not line.strip():
            continue
        if not re.fullmatch(r"import [A-Za-z0-9_.]+", line):
            return None
        imports.append(line)
    declarations = {}
    prints = []
    for chunk in chunks[1:]:
        match = re.match(r"theorem ([A-Za-z0-9_.]+)\s*:", chunk)
        if match is None or match.group(1) in declarations:
            return None
        lines = chunk.splitlines()
        body = []
        for line in lines:
            if line.startswith('#print axioms '):
                if not re.fullmatch(r"#print axioms [A-Za-z0-9_.]+", line):
                    return None
                prints.append(line)
            else:
                body.append(line)
        declarations[match.group(1)] = '\n'.join(body).strip()
    if not declarations:
        return None
    if any(line.removeprefix('#print axioms ') not in declarations for line in prints):
        return None
    return sorted(imports), declarations


def order_only_equivalent(left: str, right: str) -> bool:
    """Exact declaration bodies/imports; ordering and optional axiom prints may vary.

    This is a promotion diagnostic, not a Lean proof checker. A child selecting
    either already verified parent file must still recompile its full closure.
    """
    lhs = _parts(left)
    return lhs is not None and lhs == _parts(right)
