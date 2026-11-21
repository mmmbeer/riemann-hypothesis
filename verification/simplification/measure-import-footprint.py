#!/usr/bin/env python3
"""Measure tracked Lean sources and the imports unique to each proof branch."""
import json
import re
import subprocess
from graphlib import TopologicalSorter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
IMPORT = re.compile(rb"^(?:(?:public|private|meta)[ \t]+)*import[ \t]+(\S+)", re.M)


def closure(graph, start, omitted=()):
    pending = [start]
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        pending.extend(dep for dep in graph[module] if (module, dep) not in omitted)
    return seen


def measure():
    paths = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=ROOT)
    paths = [Path(item.decode()) for item in paths.split(b"\0") if item]
    counts = {}
    imports = {}
    total_lines = total_bytes = 0
    for path in paths:
        source = (ROOT / path).read_bytes()
        lines = source.count(b"\n")
        total_lines += lines
        total_bytes += len(source)
        if path.parts[0] == "src":
            module = ".".join(path.with_suffix("").parts[1:])
            counts[module] = lines
            imports[module] = [item.decode() for item in IMPORT.findall(source)]
    local_roots = {module.split(".")[0] for module in imports}
    graph = {name: [d for d in ds if d.split(".")[0] in local_roots] for name, ds in imports.items()}
    missing = {d for ds in graph.values() for d in ds if d not in graph}
    if missing:
        raise ValueError(f"Missing local imports: {sorted(missing)}")
    tuple(TopologicalSorter(graph).static_order())
    main = closure(graph, "Main")

    def size(modules):
        return {"files": len(modules), "lines": sum(counts[name] for name in modules)}

    def exclusive(caller, targets):
        edges = {(caller, target) for target in targets}
        if not set(targets) <= set(graph[caller]):
            raise ValueError(f"Missing expected import from {caller}")
        return size(main - closure(graph, "Main", edges))

    aa = "Development.AutomorphicArithmetic."
    row = aa + "CharacterBoxes.EveryCharacterOfRow"
    window = aa + "AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow"
    theta = aa + "ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin"
    gal = aa + "Foundations.GaloisRepresentations.IntegralStructures."
    result = {
        "tracked": {"files": len(paths), "lines": total_lines, "bytes": total_bytes},
        "main": size(main),
        "outside_main": sorted(graph.keys() - main),
        "row_exclusive": exclusive(row, [theta, window]),
        "theta_exclusive": exclusive(row, [theta]),
        "window_exclusive": exclusive(row, [window]),
        "geometry_exclusive": exclusive(gal + "RowSrc", [gal + "GeometricFlagBases.WeightOneGeometricRealization"]),
        "unconditional_row_module": size(closure(graph, gal + "RowSrc")),
    }
    if gal + "RowOfOddSeed" in graph:
        result["row_from_supplied_seed"] = size(closure(graph, gal + "RowOfOddSeed"))
    return result


if __name__ == "__main__":
    print(json.dumps(measure(), indent=2))
