#!/usr/bin/env python3
"""Render selected actual direct imports; --check requires only Python."""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SELECTED = [
    "MainResults", "Statement", "Algebra.StatementTheorem",
    "Algebra.StatementFiniteModules", "Algebra.StatementPresentation",
    "Algebra.RightModuleMagnitudePublic", "Algebra.RightModuleSimpleCount",
    "Algebra.RightModuleIntervalProof", "Algebra.RightModuleMagnitudeSurplus",
    "Algebra.RightModuleIntervalInequality", "Algebra.RightModuleIntervalEquality",
    "Algebra.RightModuleStandardIntervalBetaTransfer",
    "Algebra.RightModuleStandardIntervalBiserial",
    "Algebra.RightModuleStandardIntervalThin", "Algebra.RightModuleStandardIntervalPacking",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    names = ["MagnitudeConjecture." + name for name in SELECTED]
    edges = []
    for name in names:
        source = ROOT / (name.replace(".", "/") + ".lean")
        for target in re.findall(r"^import (\S+)", source.read_text(), re.M):
            if target in names:
                edges.append((name, target))
    lines = ['digraph imports {', 'rankdir=TB; bgcolor="#f7f6f1"; pad=0.3;',
             'node [shape=box, style="rounded,filled", fillcolor="white", color="#007d78", fontname="sans-serif", fontsize=12];',
             'edge [color="#53656d"];']
    for name in names:
        label = name.removeprefix("MagnitudeConjecture.").replace(".", "\n", 1)
        lines.append(f'{json.dumps(name)} [label={json.dumps(label)}];')
    lines.extend(f'{json.dumps(a)} -> {json.dumps(b)};' for a, b in edges)
    lines.append('}')
    dot = "\n".join(lines) + "\n"
    path = ROOT / "website/assets/public-imports.dot"
    if args.check:
        if not path.exists() or path.read_text() != dot:
            raise SystemExit("Import graph has drifted; run scripts/generate_import_graph.py with Graphviz installed")
    else:
        path.write_text(dot)
        subprocess.run(["dot", "-Tsvg", str(path), "-o", str(path.with_suffix(".svg"))], check=True)
    print(f"Selected import graph: {len(names)} modules, {len(edges)} direct imports")


if __name__ == "__main__":
    main()
