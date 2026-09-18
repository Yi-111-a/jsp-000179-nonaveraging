# JSP-000179 — Erdős–Straus non-averaging set problem

## Statement

A set of integers `A` is **non-averaging** if no element `a ∈ A` can be written
as the average of a nonempty subset of `A ∖ {a}`; equivalently, `A` avoids
solutions in distinct variables to all equations

    k·x₀ = x₁ + ⋯ + xₖ      (k ≥ 1, all variables distinct)

Let `h(n)` denote the largest size of a non-averaging subset of `[n] = {1,…,n}`.

**Theorem (Pham–Zakharov 2024/2025).** `h(n) = n^{1/4 + o(1)}`.

Equivalently, `log h(n) / log n → 1/4` as `n → ∞`.

## History

| Who | Bound |
| --- | --- |
| Straus (late 1960s) | `h(n) ≥ e^{c√log n}` |
| Erdős–Straus | `h(n) = O(n^{2/3})` |
| Erdős–Sárközy (1990) | `h(n) ≪ (n log n)^{1/2}` |
| Abbott | `h(n) = Ω(n^{1/5})` |
| Bosznay (1989) | `h(n) = Ω(n^{1/4})`, explicit parabola construction |
| Conlon–Fox–Pham (2023) | `h(n) ≤ n^{√2−1+o(1)}` |
| **Pham–Zakharov (arXiv:2410.14624v2)** | **`h(n) = n^{1/4+o(1)}`** |

## References

- [PhZa24] H. T. Pham, D. Zakharov, *Sharp bound for the Erdős–Straus
  non-averaging set problem*, arXiv:2410.14624v2 (2025). — **primary source**
- [CFP23] D. Conlon, J. Fox, H. T. Pham, *Homogeneous structures in subset sums
  and non-averaging sets*, arXiv:2311.01416 (2023). — structure theorem input
- [Bo89] A. P. Bosznay, *On the lower estimation of nonaveraging sets*,
  Acta Math. Hungar. (1989), 155–157. — lower-bound construction
- [ErSa90] P. Erdős, A. Sárközy, *On a problem of Straus* (1990).
- JSP catalog entry:
  https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000179
