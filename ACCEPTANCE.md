# Acceptance criteria — JSP-000179

The award claim requires ALL of the following gates to be green at a pinned
40-character commit SHA:

## Gates

1. **Build.** `cd lean && lake build` exits 0 with no errors.
2. **No gaps.** Zero occurrences of `sorry`, `admit`, `axiom` (user-declared),
   `native_decide`-free — i.e. `grep -rniE '\b(sorry|admit)\b' lean --include='*.lean'`
   returns 0 matches.
3. **Axioms.** `#print axioms nonaveraging_max_size_sharp` lists only the
   standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound`.
4. **Statement fidelity.** The theorem named `nonaveraging_max_size_sharp`
   states: `log h(n) / log n → 1/4` where `h(n)` is the max cardinality of a
   `NonAveraging` subset of `Finset.Icc 1 n` in `ℤ`, matching the problem in
   PROBLEM.md.
5. **Reproducibility.** `lean/lean-toolchain` pins the Lean version; the repo is
   public and owned by the claiming GitHub account; the pinned commit is a full
   40-char SHA on `main`.

## Verification

Run `bash scripts/harness.sh`. It appends a timestamped verdict block to
`HARNESS_LOG.md`. `bash scripts/status.sh` prints the machine-readable gate
status `{build, sorries, axioms, gate}`.

## Note on scope

Per the awards CONTRIBUTING.md, only a *complete* formalization is eligible:
no `sorry`/`admit`, no extra axioms. Intermediate checkpoints
(`nonaveraging_max_size_weak`, structure lemmas) are stepping stones only.
