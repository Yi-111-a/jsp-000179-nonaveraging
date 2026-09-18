# Scope

## In scope

- `NonAveraging` for `Finset ℤ` and its basic API (monotonicity, translation /
  dilation invariance, the Erdős–Straus subset-sum disjointness criterion).
- `h(n)`: maximum cardinality of a non-averaging subset of `[n]`.
- **Lower bound (proved):** Bosznay's explicit construction
  `A_q = { i·q³ + i(i+1)/2 : 1 ≤ i ≤ q−1 } ⊆ [q⁴]`, giving `h(n) ≥ n^{1/4} − O(1)`
  and hence `liminf log h / log n ≥ 1/4`.
- **Upper bound (the hard direction):** `|A| ≤ n^{1/4+o(1)}`, decomposed per
  arXiv:2410.14624v2:
  - `GAP.lean` — generalized arithmetic progressions; the Conlon–Fox–Pham
    structure theorem for subset sums (paper's Theorem 3 / Corollary 5).
  - `ConvexPosition.lean` — δ-convex position; the density-increment lemma
    (paper's Lemma 1, via linear-approximation Lemma 2).
  - `Structure.lean` — subset-sum dimension, `(δ,γ)`-irreducibility,
    down/up-moves, the intersection theorem (paper's Theorem 4).
  - `UpperBound.lean` — density-increment iteration → Theorem 2 → limsup.
- `Main.lean` — `nonaveraging_max_size_sharp`: both directions glued.

## Out of scope (v1)

- The general `d`-dimensional box result (Theorem 2 is used as an internal
  lemma for `d = 1`; the full statement may be formalized later).
- Quantitative rates for the `o(1)` term.
- Stability / characterization of extremal sets.

## Methodology notes

- Generate → machine-verify → revise loop (Aletheia-style).
- Discovery tree: each `sorry` is a frontier node; compute is concentrated on
  nodes that unblock the headline theorem.
- Branch convention `agent/<id>-<lemma>`; one `.lean` file per worker;
  harness run after every merge.
