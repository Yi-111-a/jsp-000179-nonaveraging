# Agent guide — JSP-000179

## Commands

- Build: `cd lean && lake build` (first run needs `lake exe cache get`).
- Full gate: `bash scripts/harness.sh` (appends to `HARNESS_LOG.md`).
- Quick status: `bash scripts/status.sh`.
- Always `export PATH="$HOME/.elan/bin:$PATH"` first.

## Ownership map (one file per worker)

| File | Owner | Content |
| --- | --- | --- |
| `Nonaveraging/Defs.lean` | A | `NonAveraging`, `subsetSums`, API |
| `Nonaveraging/MaxSize.lean` | A | `h`, monotonicity, extremal set |
| `Nonaveraging/Bosznay.lean` | A | Bosznay construction, `h_ge_quarter` |
| `Nonaveraging/Asymptotics.lean` | D | `log_h_div_log_lower`, tendsto glue |
| `Nonaveraging/GAP.lean` | B | GAP API, `cfp_structure` (Thm 3), `cfp_structure_cor` (Cor 5) |
| `Nonaveraging/ConvexPosition.lean` | C | δ-convex position, Lemma 1 + Lemma 2 |
| `Nonaveraging/Structure.lean` | B | `SubSumWitness`, `Irreducible`, Lemma 10, Thm 4 |
| `Nonaveraging/UpperBound.lean` | B/C | Theorem 2 → `log_h_div_log_upper` |
| `Nonaveraging/Main.lean` | D | headline theorem + squeeze form |

## Workflow

1. Branch `agent/<id>-<lemma>`; edit only your file(s); open a PR or merge to
   `main` only when `lake build` passes.
2. After every merge, run `bash scripts/harness.sh` and commit the log.
3. `main` must always build. A `sorry` is a frontier node, not a failure —
   but removing one is a breakthrough: commit immediately
   (`feat(<file>): prove <lemma>`), tag `checkpoint/<date>-<what>`.
4. For hard lemmas run 2–3 competing attempts on separate branches; keep the
   one that compiles cleanest (Aletheia generate–verify–revise loop).

## Frontier (sorry nodes, dependency order)

```
cfp_structure / cfp_structure_cor          (GAP.lean — Thm 3, Cor 5; App. A)
  └─ convex_linear_approx                  (ConvexPosition.lean — Lemma 2)
       └─ density_increment                (Lemma 1)
  └─ Irreducible / SubSumWitness API       (Structure.lean)
       └─ irreduciblization                (Lemma 10)
       └─ embedded_in_mu_convex_position   (Theorem 4)
            └─ nonaveraging_box_bound      (Theorem 2)
                 └─ log_h_div_log_upper
log_h_div_log_lower                        (Asymptotics.lean — real-analysis glue)
nonaveraging_max_size_squeeze              (Main.lean — ε-form of headline)
```

## Conventions

- No `axiom`, no `native_decide`-style escapes, no `@[implemented_by]` cheats.
- `#print axioms nonaveraging_max_size_sharp` must list only
  `propext`, `Classical.choice`, `Quot.sound`.
- `Set.InjOn`/`Finset` API follows Mathlib v4.34.0 naming; check
  `lake-manifest.json` before assuming a lemma name.
