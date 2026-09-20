# SCOPE — what is / is not proved for the prize (JSP-000179)

## Headline target

- Required theorem: `nonaveraging_max_size_sharp` (see ACCEPTANCE.md / acceptance.json)
- Status at scaffold: present as a declaration with supporting lower-bound pieces; upper-bound / structure steps still contain `sorry`.

## What the headline covers

- Full two-sided sharp asymptotic \(h(n)=n^{1/4+o(1)}\) for non-averaging subsets of \([n]\), matching PhZa24 Theorem 1 (and the matching Bosznay lower bound).

## Honest gaps vs. PhZa24 (arXiv:2410.14624)

Formalization must still close: CFP subset-sum structure applications, \(\delta\)-convexity / density-increment geometry, and the upper-bound iteration that forces the \(1/4+o(1)\) exponent. Supporting lemmas in `Nonaveraging/` may land as milestones before the headline is sorry-free.

## Prize rules reminder

Only a COMPLETE formalization of the ORIGINAL catalog problem is eligible.
Do not open award claim issues / PR TheJustinSunPrize/awards.
