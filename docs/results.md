# Results

[Back to the README](../README.md)

The results for all five cases are in the root file `SquaresInCircles.lean`,
namespace `SquaresInCircles`:

```lean
theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)

theorem uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    HasNormalForm S o (modelCenters n)
```

`optimality_attainment_uniqueness` conjoins the three. The statements use only
the definitions in [Definitions](definitions.md).

`rigid_uniqueness` restates uniqueness with the frame `pointInDirection o φ`
replaced by an explicit bijection `e` of the plane that preserves Euclidean
distance and takes the origin to `o`: under `e`, the open and the closed squares
are exactly the model squares.

Each case also stands alone, in namespaces `SquaresInCircles.One`, …,
`SquaresInCircles.Five` (folders `One/`, …, `Five/`), with the same three
theorems:

| theorem | statement, for `n = 3` |
| --- | --- |
| `Three.optimality` | `Packing S o R → Three.radius ≤ R` |
| `Three.attainment` | `∃ S o, Packing S o Three.radius` |
| `Three.uniqueness` | `Packing S o Three.radius → HasNormalForm S o Three.centers` |

`Five.polygon_uniqueness` needs only interior-disjointness and the closed 12-gon
of Step 1 in [the proof outline](proof.md), not the disk.

**Polygon relaxations.** For three and five squares the proofs go through
stronger statements that mention no disk at all:
`three_polygon_strict_impossible` and `five_polygon_strict_impossible` rule out
`n` interior-disjoint squares whose centres all satisfy the strict contact
polygon of Step 1 in [the proof outline](proof.md). For four squares,
`four_diamond_impossible` needs the closed disk as well as the strict diamond.
