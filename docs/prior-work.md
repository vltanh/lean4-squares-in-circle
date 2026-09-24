# Prior work

[Back to the README](../README.md)

This review reflects the literature as of September 2026.

## Squares in a circle

Erich Friedman's [Squares in Circles](https://erich-friedman.github.io/packing/squincir/) page has
collected the best known packings since 1997; the packings of three, five and
seven squares were found by Friedman in 1997. Before this repository, the status
was:

| n | earlier result | this repository |
| :-: | --- | --- |
| 1, 2 | folklore, listed as trivial on Friedman's page | formal proofs of optimality and uniqueness |
| 3 | computer-assisted interval enclosure of the radius and the optimal arrangements by Montanher, Neumaier, Markót, Domes and Schichl [1]; no exact value | exact formal proofs of optimality and uniqueness |
| 4 | reported on Friedman's page as proved at the International Math Summer Camp in 2026; we found no publication | formal proofs of optimality and uniqueness |
| 5 | none found; the plus is listed only as the best known packing | formal proofs of optimality and uniqueness |
| 7 | none found; the packing of radius `√13/2` is listed only as the best known one | formal proofs of optimality and of uniqueness up to the sliding of the middle column |

Montanher et al. [1] state the three-square problem as a constraint satisfaction
problem over a tiling of the configuration space and search it by interval
branch and bound, implemented in C++ with the Filib and Moore interval
libraries. Their Theorem 2 encloses the optimal radius in
`[1.28847050800547, 1.28847050800553]`, an interval of width `6·10⁻¹⁴` that
contains `5√17/16`, and every optimal arrangement in boxes of width at most
`6.23·10⁻¹³` near the T. The enclosure does not determine the radius exactly,
and does not show that the T itself is optimal. The proofs here differ in
three ways:

- **Trust.** Their result depends on the correctness of the search code and of
  the libraries' interval rounding. Here Lean's kernel checks every step, and
  no floating-point arithmetic, interval arithmetic or external solver is
  involved.
- **Exactness.** They enclose the radius and the optimal arrangements. Here the
  radius is exact, and the T is proved to be the only optimal packing, up to a
  rotation about the disk centre and a relabelling of the squares.
- **Method.** They subdivide the configuration space. Here one geometric
  argument, contact tangents and an angular budget, covers three, four and five
  squares.

Friedman's page and the Wikipedia article
[Square packing](https://en.wikipedia.org/wiki/Square_packing#In_a_circle)
(both as of September 2026) list only one, two and four squares as proved
optimal and do not record the three-square enclosure of [1]. The
[`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch of this repository holds an earlier formal proof of the three-square
lower bound, by rational certificates.

## Formal verification

Proof assistants have verified packing theorems in other settings: the Kepler
conjecture in HOL Light and Isabelle [2], and the optimal sphere packing in
dimension 8 in Lean [3]. We found no formal proof of an optimal packing of
squares or circles in a circle or a square. To our knowledge, this repository
gives the first proof-assistant verification of these six cases. We also found
no earlier exact proof of optimality for three, five or seven squares, and none
of uniqueness for three, four, five or seven squares.

## References

1. T. Montanher, A. Neumaier, M. C. Markót, F. Domes, H. Schichl. Rigorous
   packing of unit squares into a circle. *J. Global Optim.* 73 (2019)
   547–565. [doi:10.1007/s10898-018-0711-5](https://doi.org/10.1007/s10898-018-0711-5)
2. T. Hales et al. A formal proof of the Kepler conjecture.
   *Forum Math. Pi* 5 (2017) e2.
3. S. Hariharan, C. Birkbeck, S. Lee, H. K. G. Ma, B. Mehta, A. Poiroux,
   M. Viazovska. A milestone in formalization: the sphere packing problem in
   dimension 8. [arXiv:2604.23468](https://arxiv.org/abs/2604.23468) (2026).
