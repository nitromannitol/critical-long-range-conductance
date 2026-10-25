# Independent statement comparison

The manual `Independent comparators` workflow builds production once, then checks
`QuantitativeHomogenization.main_theorem` and the two `QuenchedInvariance` targets
`quenched_invariance_principle` and `quenched_invariance_principle_intro`, under
`LongRangeAudit`. Both pairs passed in the clean release checkout, including dependency
comparison, NanoDa and Lean kernel replay.

The project and standalone exporter use Lean 4.32.0; the comparator uses Lean
4.34.0-rc1. Tool source revisions are fixed in the workflow and verified by the runner.
The comparator keeps its committed Lake manifest: its internal export parser is
separate from the standalone Lean 4.32 exporter. No tool or dependency build cache
is restored; mathlib's official cache fetch is followed by a production build.

From the project root, with those tools already built:

```sh
python3 scripts/run_comparators.py \
  --comparator-dir /path/to/comparator \
  --exporter-dir /path/to/lean4export \
  --nanoda-dir /path/to/nanoda_lib \
  --landrun-dir /path/to/landrun \
  --lock "$HOME/.lake-global.lock"
```

Equivalent environment variables are `COMPARATOR_COMPARATOR_DIR`,
`COMPARATOR_EXPORTER_DIR`, `COMPARATOR_NANODA_DIR`, `COMPARATOR_LANDRUN_DIR`, and
`COMPARATOR_LOCK`. Python 3.11+, elan, git and `/usr/bin/flock` are required.
The workflow additionally installs Go 1.24.0 and Rust 1.90.0.

Every Lean/Lake/export/comparison process tree holds one exclusive lock, with
one Lean thread. Production imports resolve through this checkout's `lake env`.
Each pair gets newly compiled `SolutionBasic`, `SolutionBridge`, `Solution` and
`Challenge` modules and exports in `.lake/comparator-logs/<pair>/`. Previous pair
artifacts are removed before compilation. Solution warnings fail the run;
Challenge logs permit only the expected number of intentional theorem-hole warnings.
Logs, hashes and successful-run receipts remain there; failed runs retain their logs.

This is **trusted frontend API mode**: the script directly compiles the reviewed
files and calls the unchanged pinned `Comparator.verifyMatch` on fresh exports.
That API compares complete target dependency closures and permitted axioms, runs
NanoDa through landrun, and replays Lean's built-in kernel. The sandboxed comparator
build/export frontend is bypassed. This does not run con-ron or the newer bundled
Lean 4.35 runner. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. A successful comparison establishes agreement with the supplied
Challenge declarations; source correspondence remains a separate review.

Keep audits outside the default production glob. An optional separate Lake library
can be registered as follows (no `@[default_target]`):

```lean
lean_lib LongRangeAudit where
  globs := #[.andSubmodules `LongRangeAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
```

The runner uses targeted direct Lean compilation, so it does not require this
registration. Do not add `LongRangeAudit` to production imports or default targets.
