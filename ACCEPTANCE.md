# ACCEPTANCE — JSP-000179 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000179
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> How large can a subset of an integer interval be if no element is the average of some other elements?

The accepted answer is the sharp Erdős–Straus bound of Pham–Zakharov (arXiv:2410.14624): if \(h(n)\) is the largest size of a non-averaging subset of \(\{1,\ldots,n\}\), then
\[
h(n)=n^{1/4+o(1)}\qquad\bigl(\text{equivalently }\log h(n)/\log n\to 1/4\bigr).
\]
Weaker one-sided bounds alone (e.g. only Bosznay’s \(\Omega(n^{1/4})\) lower bound, or only a strictly larger upper exponent) are **not** the full original statement.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `nonaveraging_max_size_sharp` | \(\log h(n)/\log n \to 1/4\) (PhZa24 sharp bound; catalog answer). |

**Not sufficient for prize_ready:** one-sided lemmas, weak-exponent bounds with fixed slack, or structure lemmas alone.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.

`partial_ok` may be true for harness-green partial regimes; never treat as SUCCESS for the prize.
