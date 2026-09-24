# Results

[Back to the README](../README.md)

The results for all six cases are in the root file `SquaresInCircles.lean`,
namespace `SquaresInCircles`. Optimality and attainment cover `n = 1, …, 5`
and `n = 7`, uniqueness `n = 1, …, 5`, and `sliding_uniqueness` classifies
the optimal packings of seven squares:

```lean
theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)

theorem uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    HasNormalForm S o (modelCenters n)

theorem sliding_uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o (optimalRadius 7)) :
    ∃ c : Seven.Column, HasNormalForm S o (Seven.slidingCenters c)
```

`optimality_attainment_uniqueness` conjoins the three for `n ≤ 5`. The
statements use only the definitions in [Definitions](definitions.md).

`rigid_uniqueness` restates uniqueness with the frame `pointInDirection o φ`
replaced by an explicit bijection `e` of the plane that preserves Euclidean
distance and takes the origin to `o`: under `e`, the open and the closed squares
are exactly the model squares.

Each case also stands alone, in namespaces `SquaresInCircles.One`, …,
`SquaresInCircles.Five` and `SquaresInCircles.Seven` (folders `One/`, …,
`Five/` and `Seven/`), with the same theorems:

| theorem | statement, for `n = 3` |
| --- | --- |
| `Three.optimality` | `Packing S o R → Three.radius ≤ R` |
| `Three.attainment` | `∃ S o, Packing S o Three.radius` |
| `Three.uniqueness` | `Packing S o Three.radius → HasNormalForm S o Three.centers` |

For seven squares the optimum is not unique: `Seven.sliding_packing` shows
that the middle column of the optimal packing can take any position in a range
of total slack `2√3 - 3`, and `Seven.uniqueness` shows that these are all the
optimal packings. `Seven.packing_iff_sliding` states both directions, and
`Seven.classification_by_slots` parametrizes the family by the four gaps of
the column, nonnegative with sum `2√3 - 3`. Two stronger statements are proved
on the way. `Seven.six_exterior_squared_lower` gives `13/4 ≤ R^2` already for
six squares none of which contains the disk centre in its interior.
`Seven.marker_separation` is the pair theorem of
[seven squares](proof/seven.md#theorem-715-marker-separation), about just two
disjoint squares.

`Five.polygon_uniqueness` needs only interior-disjointness and the closed 12-gon
of [Step 1 for five squares](proof/five.md#step-1-the-contact-polygon), not the
disk.

**Polygon relaxations.** For three and five squares the proofs go through
stronger statements that mention no disk at all:
`three_polygon_strict_impossible` and `five_polygon_strict_impossible` rule out
`n` interior-disjoint squares whose centres all satisfy the strict contact
polygon of Step 1 in [the proof outline](proof/README.md#three-to-five-squares).
For four squares, `four_diamond_impossible` needs the closed disk as well as the
strict diamond.
