#!/usr/bin/env python3
"""Inspect written Lean source only. This does NOT invoke or replace Lean."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_COMMIT = "4f73fefceb73e8e707c837f55549bf864f0dfd8a"
BASE_IMPORTS = {
    "ThreeUnitSquaresInCircle.Geometry",
    "ThreeUnitSquaresInCircle.SeparatingAxes",
    "ThreeUnitSquaresInCircle.Construction",
    "ThreeUnitSquaresInCircle.Main",
}


def strip_comments_and_strings(text: str) -> str:
    """Preserve offsets/newlines; recognize nested Lean block comments."""
    chars = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            step = 1
            if text.startswith("/-", i):
                depth += 1
                step = 2
            elif text.startswith("-/", i):
                depth -= 1
                step = 2
            for j in range(i, min(i + step, len(text))):
                if chars[j] != "\n":
                    chars[j] = " "
            i += step
        elif quoted:
            if text[i] == '"':
                quoted = False
            step = 2 if text[i] == "\\" else 1
            for j in range(i, min(i + step, len(text))):
                if chars[j] != "\n":
                    chars[j] = " "
            i += step
        elif text.startswith("/-", i):
            depth = 1
            chars[i:i + 2] = [" ", " "]
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                chars[i] = " "
                i += 1
        elif text[i] == '"':
            quoted = True
            chars[i] = " "
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError("Unclosed comment or string")
    return "".join(chars)


def main() -> None:
    paths = sorted((ROOT / "ThreeUnitSquaresInCircle/Unified").glob("*.lean"))
    paths += [ROOT / "ThreeUnitSquaresInCircle/Unified.lean", ROOT / "UnifiedAxiomAudit.lean"]
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in paths}
    graph: dict[str, list[str]] = {}
    rows = []
    for module, path in modules.items():
        data = path.read_bytes()
        text = data.decode("utf-8")
        clean = strip_comments_and_strings(text)
        imports = re.findall(r"^import\s+([\w.]+)", clean, re.MULTILINE)
        unknown = set(imports) - modules.keys() - BASE_IMPORTS
        if unknown:
            raise ValueError(f"Unknown imports in {path}: {unknown}")
        graph[module] = [m for m in imports if m in modules]
        tokens = list(re.finditer(r"\b(?:sorry|admit|native_decide)\b", clean))
        rows.append({
            "path": str(path.relative_to(ROOT)),
            "lines": len(text.splitlines()),
            "git_blob_sha": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
            "sha256": hashlib.sha256(data).hexdigest(),
            "imports": imports,
            "markers": [{"token": t.group(), "line": text.count("\n", 0, t.start()) + 1} for t in tokens],
            "custom_axiom_declarations": len(re.findall(r"^\s*axiom\s+", clean, re.MULTILINE)),
        })
    visited, active = set(), set()
    def visit(module: str) -> None:
        if module in active:
            raise ValueError(f"Local import cycle at {module}")
        if module in visited:
            return
        active.add(module)
        for dep in graph[module]:
            visit(dep)
        active.remove(module)
        visited.add(module)
    for module in graph:
        visit(module)
    markers = [(r["path"], m) for r in rows for m in r["markers"]]
    report = {
        "scope": "Textual source inspection, NOT Lean verification",
        "base_commit": BASE_COMMIT,
        "compiler_invoked": False,
        "lean_acceptance": "not tested",
        "lean_file_count": len(rows),
        "lean_line_count": sum(r["lines"] for r in rows),
        "sorry_count": sum(m["token"] == "sorry" for _, m in markers),
        "admit_count": sum(m["token"] == "admit" for _, m in markers),
        "native_decide_count": sum(m["token"] == "native_decide" for _, m in markers),
        "custom_axiom_declarations": sum(r["custom_axiom_declarations"] for r in rows),
        "local_import_cycles": False,
        "unknown_imports": [],
        "files": rows,
    }
    out = ROOT / "docs/UNIFIED_SOURCE_INSPECTION.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2))


if __name__ == "__main__":
    main()
