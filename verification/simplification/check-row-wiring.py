#!/usr/bin/env python3
"""Check the row proof's composition against the recorded Lean 4.33.1 interfaces."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "src" / "Development" / "AutomorphicArithmetic"
THETA = SOURCE / "ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries"
WINDOW = SOURCE / "AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean"
ROW = SOURCE / "CharacterBoxes/EveryCharacterOfRow.lean"
EXPLICIT_ROW = "UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc"
ROW_ALIAS = "UpperTheory.One.M.Row"


def fixture_source(data):
    # These premises exist only in a temporary, standalone Lean environment.
    lines = ["import Lean", "set_option autoImplicit false", "set_option linter.unusedVariables false"]
    for name in data["opaque_propositions"]:
        lines.append(f"opaque {name} : Prop")
    for name, target in data["aliases"].items():
        lines.append(f"abbrev {name} := {target}")
    for name, fields in data["structures"].items():
        lines.append(f"structure {name} : Prop where")
        lines.extend(f"  {field} : {ty}" for field, ty in fields.items())
    for name, ty in data["premises"].items():
        lines.append(f"axiom {name} : {ty}")
    return "\n".join(lines)


def checked_proofs(data):
    files = [(THETA / name).read_text() for name in
             ("RowLiteratureInputs.lean", "EveryCharacterOfLiteratureOfVWin.lean")]
    proofs = []
    helpers = data["checked_helpers"]
    seen = set()
    command = re.compile(r"^theorem ([\w.']+) .*?(?=^\S|\Z)", re.M | re.S)
    for source in files:
        for match in command.finditer(source):
            name = match[1]
            if name not in helpers:
                continue
            if name in seen:
                raise ValueError(f"Duplicate definition of {name}")
            seen.add(name)
            proofs.extend([match[0].strip(), f"example : {helpers[name]} := {name}"])
    if missing := helpers.keys() - seen:
        raise ValueError(f"Missing helper definitions: {sorted(missing)}")
    window = WINDOW.read_text().split("namespace UpperTheory.LiteratureTheorems\n", 1)[1]
    row = ROW.read_text().split("\ntheorem ", 1)[1]
    assembly = "namespace UpperTheory.LiteratureTheorems\n" + window + "\ntheorem " + row
    if assembly.count(EXPLICIT_ROW) != 2:
        raise ValueError("Check the two row signatures against their recorded kernel types")
    proofs.append(assembly.replace(EXPLICIT_ROW, ROW_ALIAS))
    proofs.append(f"example : {ROW_ALIAS} → UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter_of_row")
    return "\n\n".join(proofs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="path to Lean 4.33.1")
    args = parser.parse_args()
    version = subprocess.check_output([args.lean, "--version"], text=True)
    if "version 4.33.1," not in version:
        raise ValueError(f"Expected Lean 4.33.1, found {version.strip()}")
    data = json.loads((HERE / "row-interface.json").read_text())
    source = fixture_source(data) + "\n\n" + checked_proofs(data)
    with tempfile.TemporaryDirectory() as work:
        check = Path(work) / "Check.lean"
        check.write_text(source)
        subprocess.run([args.lean, str(check)], check=True)
        wrong = source.replace("gal := N.aut.car", "gal := N.aut.gal")
        if wrong == source:
            raise ValueError("The negative control no longer exercises the row projection")
        check.write_text(wrong)
        result = subprocess.run([args.lean, str(check)], capture_output=True, text=True)
        output = result.stdout + result.stderr
        if result.returncode == 0 or not all(s in output for s in ("Type mismatch", "PairUAlt", "RowT")):
            raise ValueError("The negative control failed to distinguish the two Galois hypotheses")
    print("Row and window proofs type-check against the recorded inputs. The incorrect Galois projection is rejected.")


if __name__ == "__main__":
    main()
