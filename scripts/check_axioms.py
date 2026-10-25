#!/usr/bin/env python3
"""Check the kernel axiom closure of every public statement export."""
from pathlib import Path
import re
import subprocess
import tempfile

EXPORTS = ['LongRange.Statements.lattice_sums', 'LongRange.Statements.path_counting', 'LongRange.Statements.single_scale_estimate', 'LongRange.Statements.poincare', 'LongRange.Statements.corrector_monotonicity', 'LongRange.Statements.corrector_energy_bound', 'LongRange.Statements.corrector_domain_bound', 'LongRange.Statements.hoeffding_infinite', 'LongRange.Statements.mcdiarmid', 'LongRange.Statements.quenched_invariance_principle', 'LongRange.Statements.quenched_invariance_principle_intro', 'LongRange.Statements.tightness', 'LongRange.Statements.main_theorem', 'LongRange.Statements.heatkernel_onDiagonal', 'LongRange.Statements.heatkernel_offDiagonal', 'LongRange.Statements.aldous', 'LongRange.Statements.corrector_linear_quadratic', 'LongRange.Statements.corrector_energy_lower_bound', 'LongRange.Statements.critical_dual_norm', 'LongRange.Statements.critical_dual_characterization', 'LongRange.Statements.rescaled_density', 'LongRange.Statements.rescaled_killed_density', 'LongRange.Statements.rescaled_kernel', 'LongRange.Statements.solenoidal_equivalence', 'LongRange.Statements.annulus_limit', 'LongRange.Statements.weak_scaling_obstruction']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
root = Path(__file__).resolve().parents[1]
text = "import LongRange.Statements\n" + "".join(
    "#print axioms " + name + "\n" for name in EXPORTS)
with tempfile.TemporaryDirectory(prefix="longrange-axioms-") as directory:
    source = Path(directory) / "Axioms.lean"
    source.write_text(text)
    result = subprocess.run(
        ["/usr/bin/flock", "-x", str(Path.home() / ".lake-global.lock"),
         "lake", "env", "lean", str(source)],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
if re.search(r"\b(?:warning|error):", result.stdout):
    raise SystemExit("Unexpected Lean diagnostic")
seen = set()
for name, axioms in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout):
    unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {unexpected}")
    seen.add(name)
# Lean may print the axiom-free form rather than an empty list.
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", result.stdout))
if seen != set(EXPORTS):
    raise SystemExit(f"Incomplete axiom output: missing {set(EXPORTS) - seen}")
print(f"Checked {len(seen)} public exports")
