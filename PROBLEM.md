# JSP-000179 — How large can a subset of an integer interval be if no element is the average of some other elements?

- **id:** JSP-000179
- **title:** How large can a subset of an integer interval be if no element is the average of some other elements?
- **area:** Additive combinatorics
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

How large can a subset of an integer interval be if no element is the average of some other elements?

Equivalently: let \(h(n)\) be the maximum size of a *non-averaging* subset of \(\{1,\ldots,n\}\) (no element is the average of a nonempty subset of the remaining elements). Determine the growth of \(h(n)\).

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000179
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [PhZa24] Sharp bound for the Erdős–Straus non-averaging set problem — arXiv:2410.14624 (2024). **Main formalization source.**
- [CFP23] Homogeneous structures in subset sums and non-averaging sets — arXiv:2311.01416.
- [Bo89] On the lower estimation of nonaveraging sets — Acta Math. Hungar. (1989).
- [ErSa90] On a problem of Straus — Disorder in physical systems (1990).

## Accepted mathematical answer

\[
h(n)=n^{1/4+o(1)},
\]
i.e. \(\log h(n)/\log n \to 1/4\) (Pham–Zakharov). Bosznay’s construction gives the matching \(\Omega(n^{1/4})\) lower bound.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
- No new axioms beyond standard Lean axioms
