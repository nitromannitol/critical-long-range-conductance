#!/usr/bin/env python3
"""Check the kernel axiom closure of every public statement export."""
from pathlib import Path
import os
import re
import shlex
import subprocess
import tempfile

EXPORTS = ['LongRange.Statements.lattice_sums', 'LongRange.Statements.path_counting', 'LongRange.Statements.single_scale_estimate', 'LongRange.Statements.poincare', 'LongRange.Statements.corrector_monotonicity', 'LongRange.Statements.corrector_energy_bound', 'LongRange.Statements.corrector_domain_bound', 'LongRange.Statements.hoeffding_infinite', 'LongRange.Statements.mcdiarmid', 'LongRange.Statements.quenched_invariance_principle', 'LongRange.Statements.quenched_invariance_principle_intro', 'LongRange.Statements.tightness', 'LongRange.Statements.main_theorem', 'LongRange.Statements.heatkernel_onDiagonal', 'LongRange.Statements.heatkernel_offDiagonal', 'LongRange.Statements.aldous', 'LongRange.Statements.corrector_linear_quadratic', 'LongRange.Statements.corrector_energy_lower_bound', 'LongRange.Statements.critical_dual_norm', 'LongRange.Statements.critical_dual_characterization', 'LongRange.Statements.rescaled_density', 'LongRange.Statements.rescaled_killed_density', 'LongRange.Statements.rescaled_kernel', 'LongRange.Statements.solenoidal_equivalence', 'LongRange.Statements.annulus_limit', 'LongRange.Statements.weak_scaling_obstruction']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
root = Path(__file__).resolve().parents[1]
heat_files = sorted((root / "LongRangeHeat/Statements").glob("*.lean"))
if not heat_files:
    raise SystemExit("No heat statement modules found")
imports = []
for path in heat_files:
    source = path.read_text()
    if re.findall(r"^namespace\s+([^\s]+)", source, re.MULTILINE) != [
        "LongRangeHeat.Statements"
    ]:
        raise SystemExit(f"Unexpected namespace in {path}")
    declaration_line = re.compile(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|instance)\b.*$",
        re.MULTILINE)
    declaration = re.compile(
        r"^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|opaque|axiom|"
        r"structure|class|inductive)\s+([\w']+)\b")
    declarations = []
    for line in declaration_line.findall(source):
        match = declaration.match(line.strip())
        if not match:
            raise SystemExit(f"Unsupported declaration syntax in {path}: {line.strip()}")
        declarations.append(match.group(1))
    if not declarations:
        raise SystemExit(f"No declarations found in {path}")
    EXPORTS.extend("LongRangeHeat.Statements." + name for name in declarations)
    imports.append("import LongRangeHeat.Statements." + path.stem + "\n")
if len(EXPORTS) != len(set(EXPORTS)):
    raise SystemExit("Duplicate export name")
text = "import LongRange.Statements\n" + "".join(imports) + "".join(
    "#print axioms " + name + "\n" for name in EXPORTS)
with tempfile.TemporaryDirectory(prefix="longrange-axioms-") as directory:
    source = Path(directory) / "Axioms.lean"
    source.write_text(text)
    runner = shlex.split(os.environ.get("LEAN_RUNNER", "")) or [
        "/usr/bin/flock", "-x", str(Path.home() / ".lake-global.lock"),
        "lake", "env", "lean"]
    result = subprocess.run(
        runner + [str(source)],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if result.returncode:
    print(result.stdout, end="")
    raise SystemExit(result.returncode)
output = result.stdout
if os.environ.get("LEAN_RUNNER_LOG") == "1":
    match = re.search(r"— log: ([^\n]+)", output)
    if not match:
        raise SystemExit("Lean runner did not report a log path")
    output = Path(match.group(1)).read_text()
print(output, end="")
if re.search(r"^error:|:\d+:\d+: error:|"
             r"^warning: (?:.*/)?(?:LongRange|LongRangeHeat|LongRangeAudit)/|"
             r"^(?:.*/)?(?:LongRange|LongRangeHeat|LongRangeAudit)/.*:\d+:\d+: warning:",
             output, re.MULTILINE):
    raise SystemExit("Unexpected Lean diagnostic")
seen = set()
for name, axioms in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output):
    unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {unexpected}")
    seen.add(name)
# Lean may print the axiom-free form rather than an empty list.
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", output))
if seen != set(EXPORTS):
    raise SystemExit(f"Incomplete axiom output: missing {set(EXPORTS) - seen}")
print(f"Checked {len(seen)} public exports")
