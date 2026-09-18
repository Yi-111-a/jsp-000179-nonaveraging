# JSP-000179 — Lean formalization

Formalization in Lean 4 / Mathlib of the Pham–Zakharov sharp bound for the
Erdős–Straus non-averaging set problem:

> `h(n)`, the maximum size of a non-averaging subset of `{1,…,n}`, satisfies
> `h(n) = n^{1/4 + o(1)}`.

- Problem: [PROBLEM.md](PROBLEM.md) ·
  [JSP-000179](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000179)
- Acceptance gates: [ACCEPTANCE.md](ACCEPTANCE.md)
- Proof decomposition / scope: [SCOPE.md](SCOPE.md)
- Verification log: [HARNESS_LOG.md](HARNESS_LOG.md)

## Layout

```
lean/
  lean-toolchain          leanprover/lean4:v4.34.0
  lakefile.lean           Mathlib v4.34.0 dependency
  Nonaveraging.lean       root import
  Nonaveraging/
    Defs.lean             NonAveraging + subsetSums + Erdős–Straus criterion
    MaxSize.lean          h(n) and basic bounds
    Bosznay.lean          lower-bound construction (PROVED: h(q⁴) ≥ q−1)
    Asymptotics.lean      liminf ≥ 1/4 glue
    GAP.lean              GAPs + CFP structure theorem (frontier)
    ConvexPosition.lean   δ-convex position + density increment (frontier)
    Structure.lean        subset-sum dimension + irreducibility + Thm 4 (frontier)
    UpperBound.lean       Theorem 2 → limsup ≤ 1/4 (frontier)
    Main.lean             nonaveraging_max_size_sharp
scripts/
  harness.sh              build + sorry count + axiom check → HARNESS_LOG.md
  status.sh               {build, sorries, axioms, gate}
```

## Verify

```bash
cd lean && lake build
bash scripts/harness.sh
bash scripts/status.sh
```

Source: Pham–Zakharov, *Sharp bound for the Erdős–Straus non-averaging set
problem*, arXiv:2410.14624v2.
