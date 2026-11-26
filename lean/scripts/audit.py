"""Check the axioms of the targets and expose their full elaborated types."""
from pathlib import Path
import argparse
import csv
import json
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.M)
INPUTS = re.compile(r"CHECK_INPUTS\|([^|\n]+)\|([^|\n]*)\|END")
LABELS = {"TrinomialDiskCheck": "G1", "QuinticChartCheck": "F1", "SexticChartCheck": "E10"}


def read_claims():
    with (ROOT / "CLAIM_MAP.tsv").open() as source:
        return list(csv.DictReader(source, delimiter="\t"))


def check_axioms(names):
    probe = ["import Turan", "import Lean", "set_option pp.universes false",
             (ROOT / "scripts/audit_inputs.lean.inc").read_text()]
    for name in names:
        probe.extend([f"#check {name}", f"#print axioms {name}", f"run_cmd TuranAudit.report ``{name}"])
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "ClaimTypes.lean"
        source.write_text("\n".join(probe) + "\n")
        result = subprocess.run(["lake", "env", "lean", "-j1", str(source)], cwd=ROOT,
                                check=True, stdout=subprocess.PIPE, text=True)
    print(result.stdout, end="")
    entries = AXIOMS.findall(result.stdout)
    if [name for name, _ in entries] != names:
        raise ValueError("Lean did not report exactly the requested declarations in order")
    axioms = {name: sorted(s.strip() for s in items.split(",") if s.strip()) for name, items in entries}
    for name, deps in axioms.items():
        if set(deps) - STANDARD:
            raise ValueError(f"{name} uses additional axioms: {deps}")
    checked = INPUTS.findall(result.stdout)
    if [name for name, _ in checked] != names:
        raise ValueError("Lean did not report the certificate inputs for every declaration")
    inputs = {name: sorted(v.removeprefix("Turan.") for v in values.split(",") if v)
              for name, values in checked}
    return axioms, inputs


def report(claims):
    lines = ["# Paper claim audit", "", "The anchors and line numbers refer to the frozen short paper v5.40, TeX MD5 `a86117bef89fac427fade04217bf1ba4`. The claim map quotes the printed passages.",
             "", "| Place | Source anchor | Lines | Claim | Status | Lean declarations |", "|---|---|---|---|---|---|"]
    for row in claims:
        targets = ", ".join(f"`{name}`" for name in row["declarations"].split())
        lines.append(f"| {row['place']} | {row['anchor']} | {row['lines']} | {row['claim']} | {row['status']} | {targets} |")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the checked audit files")
    options = parser.parse_args()
    claims = read_claims()
    if not claims or len({row["place"] for row in claims}) != len(claims):
        raise ValueError("The paper map must have a distinct place for each row")
    names = sorted({name for row in claims for name in row["declarations"].split()})
    if not names:
        raise ValueError("Empty Lean target list")
    axioms, inputs = check_axioms(names)
    for row in claims:
        if row["status"].startswith("PROVED") != bool(row["declarations"].strip()):
            raise ValueError(f"Inconsistent target list for {row['place']}")
        actual = {LABELS.get(code, code) for name in row["declarations"].split() for code in inputs[name]}
        expected = {s.strip() for s in row["status"].removeprefix("PROVED GIVEN ").split(",")} \
            if row["status"].startswith("PROVED GIVEN ") else set()
        if actual != expected:
            raise ValueError(f"{row['place']}: certificate inputs {actual} differ from {expected}")
    products = {"CLAIMS.json": json.dumps({"paper": claims, "axioms": axioms, "inputs": inputs}, indent=2,
                                          ensure_ascii=False) + "\n", "AUDIT.md": report(claims)}
    for filename, content in products.items():
        path = ROOT / filename
        if options.write:
            path.write_text(content)
        elif path.read_text() != content:
            raise ValueError(f"{filename} differs from the checked result")
    print(f"Checked {len(names)} Lean declarations against the three permitted standard axioms.")


if __name__ == "__main__":
    main()
