"""Apply the published deletion ranges to their measured baseline checkout."""
import csv
import gzip
from itertools import groupby
from pathlib import Path
import subprocess
import sys

baseline = "0f8a0bca44c2fe3301ba4738dd7f399f56bedac5"
root = Path(sys.argv[1]).resolve()
git = ["git", "-C", str(root)]
if subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip() != baseline:
    sys.exit("Use a clean checkout of " + baseline)
changed = subprocess.check_output([*git, "status", "--porcelain", "--", "src"])
if changed:
    sys.exit("The checkout has source changes")
manifest = Path(sys.argv[2])
with gzip.open(manifest, "rt", newline="") as stream:
    rows = csv.DictReader(stream, delimiter="\t")
    for file, commands in groupby(rows, key=lambda r: r["baseline_path"]):
        target = (root / file).resolve()
        if not target.is_relative_to(root / "src") or target.suffix != ".lean":
            raise ValueError(file)
        lines = target.read_bytes().splitlines(keepends=True)
        output = []
        cursor = 0
        def retain(segment):
            if cursor and output and not output[-1].strip():
                while segment and not segment[0].strip():
                    segment = segment[1:]
            output.extend(segment)
        for command in commands:
            first = int(command["first_line"]) - 1
            last = int(command["last_line"])
            if not cursor <= first < last <= len(lines):
                raise ValueError(command)
            retain(lines[cursor:first])
            cursor = last
        retain(lines[cursor:])
        if not any(line.strip() for line in lines[cursor:]):
            while output and not output[-1].strip():
                output.pop()
        target.write_bytes(b"".join(output))
