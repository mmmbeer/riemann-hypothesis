#!/usr/bin/env python3
"""Check the removal manifest against the original source and the v0.2 kernel data."""
import argparse
import csv
import gzip
import hashlib
from collections import defaultdict
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("baseline", type=Path, help="fork at 0f8a0bca")
parser.add_argument("original", type=Path, help="original submission at 40e56bab")
parser.add_argument("dataset", type=Path, help="directory with the two v0.2 CSV archives")
args = parser.parse_args()

for filename, expected in {
    "decls.csv.gz": "af5daf53fdb72862666665eaf02a6f22b3307d5e0d175e3864d37a1ebcc9b4db",
    "decl_edges.csv.gz": "0e450a0120add04c917c574150a2898db6c07c87e1da9623d2eafe506ddc2025",
}.items():
    with (args.dataset / filename).open("rb") as stream:
        if hashlib.file_digest(stream, "sha256").hexdigest() != expected:
            raise ValueError(f"Wrong v0.2 asset: {filename}")

manifest = Path(__file__).with_name("unused-declarations.tsv.gz")
commands = {}
with gzip.open(manifest, "rt", newline="") as stream:
    baseline_lines = []
    last_file = None
    for row in csv.DictReader(stream, delimiter="\t"):
        file = row["baseline_path"]
        if file != last_file:
            baseline_lines = (args.baseline / file).read_bytes().splitlines(keepends=True)
            last_file, end = file, 0
        first, last = int(row["first_line"]) - 1, int(row["last_line"])
        name = row["declaration"]
        if name in commands or not end <= first < last <= len(baseline_lines):
            raise ValueError(row)
        commands[name] = hashlib.sha256(b"".join(baseline_lines[first:last])).digest()
        end = last

selected = defaultdict(list)
required = defaultdict(list)
with gzip.open(args.dataset / "decls.csv.gz", "rt", newline="") as stream:
    for row in csv.DictReader(stream):
        name = row["decl"]
        interval = int(row["start_line"]) - 1, int(row["end_line"])
        used = row["in_cone"] == "true" or row["n_shared_aux_in_cone"] != "0"
        if name in commands:
            if used or row["decls_in_command"] != "1" or row["generated"] != "false":
                raise ValueError(f"Required or compound declaration: {name}")
            selected[row["file"]].append((*interval, name))
        elif used:
            required[row["file"]].append(interval)

seen = set()
for file, ranges in selected.items():
    lines = (args.original / file).read_bytes().splitlines(keepends=True)
    keep = sorted(required[file])
    index = 0
    for first, last, name in sorted(ranges):
        while index < len(keep) and keep[index][1] <= first:
            index += 1
        if index < len(keep) and keep[index][0] < last:
            raise ValueError(f"{name} overlaps a used declaration or auxiliary")
        if hashlib.sha256(b"".join(lines[first:last])).digest() != commands[name]:
            raise ValueError(f"The command for {name} differs from the baseline")
        seen.add(name)
if seen != commands.keys():
    raise ValueError("The export lacks one or more manifest declarations")

with gzip.open(args.dataset / "decl_edges.csv.gz", "rt", newline="") as stream:
    rows = csv.reader(stream)
    if next(rows) != ["src", "src_kind", "dst", "dst_kind", "via"]:
        raise ValueError("Unexpected declaration edge schema")
    for source, kind, target, target_kind, _ in rows:
        if target_kind == "decl" and target in commands and (kind != "decl" or source not in commands):
            raise ValueError(f"A surviving declaration references {target}: {source}")
print(f"Verified {len(commands):,} source commands and their incoming kernel edges")
