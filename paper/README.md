# Paper source

`critical-long-range-rw.tex` is the unchanged arXiv:2604.21143v1 source, SHA-256
`1fec0f85e16b4cfddfa9cd26884efd0b00241bf1520c7790eadf47cd4a5a1627`.
`critical-long-range-rw-revised.tex` is the corrected companion. Both require the included
`critical_rw_convergence.pdf` figure. The bibliography is embedded; no external `.bib`
file is needed. Standard AMS LaTeX, geometry, hyperref, graphicx, xcolor, mathtools and
TikZ packages are required.

From this directory, a standard compilation command is:

```sh
latexmk -pdf critical-long-range-rw-revised.tex
```

The [compiled corrected article](critical-long-range-rw-revised.pdf) has 30 pages.
Paper publication licensing remains to be specified by the authors.

`CHANGES.diff` is the complete surgical diff against the original source. It records the
existing corrections and proof-route notes C1–C3, G1, O2–O6, R1 and A1, the finite-horizon
stopping-filtration clarification, the uniformization rate, the replacement off-diagonal
proof and the added Chen–Kim–Kumagai–Wang bibliography entry. No additional mathematical
prose was introduced in this packaging. The sole edit to the supplied corrected companion
is the public Lean identifier prefix `LongRange.Statements` in its formal counterpart.
The abstract and all three theorem environments are byte-identical to the original.
