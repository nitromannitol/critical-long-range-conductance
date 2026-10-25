#!/usr/bin/env python3
"""Fresh, sequential audit builds and pinned Comparator.verifyMatch API replays."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess

PROJECT_TOOLCHAIN = "leanprover/lean4:v4.32.0"
COMPARATOR_TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
PINS = {
    "comparator": "575674928e239f5bc452aab72d1dd7b0f1326494",
    "exporter": "4e7915201d3f9f04470d9eae002fa695f7cdc589",
    "nanoda": "6ae1f0cd962f081f6c423454c5da729d841236a7",
    "landrun": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
}
PAIRS = {
    "QuantitativeHomogenization": ["main_theorem"],
    "QuenchedInvariance": ["quenched_invariance_principle",
                          "quenched_invariance_principle_intro"],
}
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
]
BUILTINS = ["Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift",
            "Quot.ind"]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def git_revision(path):
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                   text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    for name in PINS:
        parser.add_argument(f"--{name}-dir", type=Path,
                            default=os.environ.get(f"COMPARATOR_{name.upper()}_DIR"))
    parser.add_argument("--lock", type=Path,
                        default=os.environ.get("COMPARATOR_LOCK",
                                               str(Path.home() / ".lake-global.lock")))
    args = parser.parse_args()
    project = args.project.resolve()
    lock = args.lock.expanduser().resolve()
    lock.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "1"
    env["LAKE_JOBS"] = "1"
    dirs = {}
    for name, revision in PINS.items():
        path = getattr(args, f"{name}_dir")
        if path is None:
            parser.error(f"--{name}-dir or COMPARATOR_{name.upper()}_DIR is required")
        dirs[name] = path.expanduser().resolve()
        if git_revision(dirs[name]) != revision:
            raise RuntimeError(f"Wrong {name} source revision")
        if subprocess.check_output(
            ["git", "-C", str(dirs[name]), "status", "--porcelain", "--untracked-files=no"],
            text=True,
        ).strip():
            raise RuntimeError(f"Modified tracked {name} sources")
    for path, toolchain in [(project, PROJECT_TOOLCHAIN),
                            (dirs["exporter"], PROJECT_TOOLCHAIN),
                            (dirs["comparator"], COMPARATOR_TOOLCHAIN)]:
        if (path / "lean-toolchain").read_text().strip() != toolchain:
            raise RuntimeError(f"Unexpected toolchain in {path.name}")

    def command(argv, cwd, log, command_env=env, output=None):
        # One process tree per lock; never a persistent shell or a nested flock.
        wrapped = ["/usr/bin/flock", "-x", str(lock), *map(str, argv)]
        with log.open("w") as report:
            report.write(shlex.join(wrapped) + "\n")
            report.flush()
            if output is None:
                subprocess.run(wrapped, cwd=cwd, env=command_env, stdout=report,
                               stderr=subprocess.STDOUT, check=True)
            else:
                with output.open("wb") as exported:
                    subprocess.run(wrapped, cwd=cwd, env=command_env, stdout=exported,
                                   stderr=report, check=True)

    logs = project / ".lake/comparator-logs"
    logs.mkdir(parents=True, exist_ok=True)

    def lake_path(cwd, toolchain, name):
        output = logs / f"{name}-lean-path.txt"
        command(["elan", "run", toolchain, "lake", "env", "printenv", "LEAN_PATH"],
                cwd, logs / f"{name}-lake-env.log", output=output)
        parts = output.read_text().strip().split(os.pathsep)
        if not all(parts):
            raise RuntimeError("lake env returned an empty search path")
        resolved = [str((cwd / part).resolve()) for part in parts]
        own = str((cwd / ".lake/build/lib/lean").resolve())
        if own not in resolved:
            raise RuntimeError("lake env omitted the package's own module directory")
        # Both tools contain Main. The comparator's entry module must precede
        # its export-parser dependency's unrelated Main module.
        return os.pathsep.join([own] + [part for part in resolved if part != own])

    # Invalidate every prior receipt before attempting either pair or tool invocation.
    for pair in PAIRS:
        work = logs / pair
        if work.is_symlink():
            raise RuntimeError("Refusing a symlinked audit log directory")
        if work.exists():
            shutil.rmtree(work)
        work.mkdir()

    project_path = lake_path(project, PROJECT_TOOLCHAIN, "project")
    comparator_path = lake_path(dirs["comparator"], COMPARATOR_TOOLCHAIN, "comparator")
    exporter = dirs["exporter"] / ".lake/build/bin/lean4export"
    nanoda = dirs["nanoda"] / "target/release/nanoda_bin"
    landrun = dirs["landrun"] / "landrun"
    for binary in [exporter, nanoda, landrun]:
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise RuntimeError(f"Missing executable: {binary}")
    driver = Path(__file__).with_name("CompareExports.lean").resolve()
    for pair, names in PAIRS.items():
        print(f"Checking {pair}", flush=True)
        namespace = f"LongRangeAudit.{pair}"
        source = project / "LongRangeAudit" / pair
        config = json.loads((source / "comparator.json").read_text())
        expected = {
            "challenge_module": namespace + ".Challenge",
            "solution_module": namespace + ".Solution",
            "theorem_names": [namespace + "." + name for name in names],
            "permitted_axioms": AXIOMS,
            "enable_nanoda": True,
        }
        if config != expected:
            raise RuntimeError(f"Unexpected configuration for {pair}")
        work = logs / pair
        (work / "comparator.json").write_text(json.dumps(config, indent=2) + "\n")
        shutil.copyfile(driver, work / "CompareExports.lean")
        audit_lib = work / "lib/lean"
        module_dir = audit_lib / "LongRangeAudit" / pair
        module_dir.mkdir(parents=True)
        audit_env = env | {"LEAN_PATH": str(audit_lib) + os.pathsep + project_path}
        sources = {}
        built = set()
        visiting = set()

        def build_module(module):
            if module in built:
                return
            if module in visiting:
                raise RuntimeError(f"Audit import cycle: {module}")
            visiting.add(module)
            relative = Path(*module.split(".")).with_suffix(".lean")
            lean_file = project / relative
            # Independent vocabulary can be organized into small local modules.
            # The production dependency closure is already built in this checkout.
            for line in lean_file.read_text().splitlines():
                line = line.strip()
                if not line:
                    continue
                if not line.startswith("import "):
                    break
                for dependency in line.removeprefix("import ").split():
                    if dependency.startswith(namespace + "."):
                        build_module(dependency)
            sources[str(lean_file.relative_to(project))] = digest(lean_file)
            argv = ["elan", "run", PROJECT_TOOLCHAIN, "lean", "-DautoImplicit=false",
                    "-DrelaxedAutoImplicit=false"]
            challenge = module == namespace + ".Challenge"
            if not challenge:
                argv.append("-DwarningAsError=true")
            olean = audit_lib / relative.with_suffix(".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            log = work / (module.removeprefix(namespace + ".") + "-build.log")
            command(argv + ["-o", str(olean), str(lean_file)], project, log, audit_env)
            if challenge:
                warnings = [line for line in log.read_text()
                            .splitlines()[1:] if "warning:" in line]
                if len(warnings) != len(names) or any(
                    line.split("warning:", 1)[1].strip() not in
                    ("declaration uses `sorry`", "declaration uses 'sorry'")
                    for line in warnings
                ):
                    raise RuntimeError("Unexpected Challenge warnings; inspect quarantined log")
            visiting.remove(module)
            built.add(module)

        # Every audit module is compiled once from source into this fresh pair directory.
        for module in ["SolutionBasic", "SolutionBridge", "Solution", "Challenge"]:
            build_module(namespace + "." + module)
        targets = BUILTINS + config["theorem_names"] + AXIOMS + PRIMITIVES
        for module in ["Challenge", "Solution"]:
            command([str(exporter), namespace + "." + module, "--", *targets], project,
                    work / f"{module}-export.log", audit_env, work / f"{module}.ndjson")
        compare_env = env | {
            "LEAN_PATH": comparator_path,
            "COMPARATOR_NANODA": str(nanoda), "COMPARATOR_LANDRUN": str(landrun),
        }
        command(["elan", "run", COMPARATOR_TOOLCHAIN, "lean", "-DwarningAsError=true",
                 str(work / "CompareExports.lean")], work, work / "comparator.log", compare_env)
        result = (work / "comparator.log").read_text()
        for marker in ["nanoda kernel accepts the solution",
                       "Lean default kernel accepts the solution",
                       "Comparator.verifyMatch completed successfully"]:
            if marker not in result:
                raise RuntimeError(f"Missing acceptance output: {marker}")
        receipt = {
            "mode": "Comparator.verifyMatch API; trusted build/export frontend",
            "pair": pair, "targets": config["theorem_names"], "tool_revisions": PINS,
            "project_toolchain": PROJECT_TOOLCHAIN,
            "comparator_toolchain": COMPARATOR_TOOLCHAIN,
            "executables_sha256": {str(p.relative_to(dirs[name])): digest(p)
                                   for name, p in [("exporter", exporter),
                                                   ("nanoda", nanoda),
                                                   ("landrun", landrun)]},
            "sources_sha256": sources,
            "files_sha256": {str(p.relative_to(work)): digest(p)
                             for p in sorted(work.rglob("*")) if p.is_file()},
        }
        (work / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"Accepted {pair}; logs: {work}", flush=True)


if __name__ == "__main__":
    main()
