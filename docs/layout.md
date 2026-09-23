# Layout

[Back to the README](../README.md)

```text
SquaresInCircles.lean      optimalRadius, and all five cases in one statement
SquaresInCircles/
├── Geometry.lean          the statement: squares, disks, Packing, normal forms
├── Common/                tools shared by several cases
├── One/                   n = 1
├── Two/                   n = 2
├── Three/                 n = 3
├── Four/                  n = 4
└── Five/                  n = 5
```

Every case folder has the same three core files: `Construction.lean` (the
radius, the optimal packing and its centres), `Optimality.lean` (the lower
bound) and `Uniqueness.lean`. Three, four and five squares add the same three
helper files for the arc argument: `Tangents.lean` (the contact polygon),
`Exterior.lean` (arcs of the squares that do not contain the disk centre) and
`Containing.lean` (the square that does). No case imports another: each
imports only `Common/` and its own folder.

## `Common/`

| File | Contents |
| --- | --- |
| `Basic.lean` | Vector operations, square frames and vertices, `InteriorDisjoint`, the farthest-vertex bound `phi` |
| `Tangents.lean` | Tangent identity; the octagon shared by four and five squares |
| `Separation.lean` | Hahn–Banach supporting functional for two squares with disjoint interiors |
| `Support.lean` | Octagon support for every normal; the radial sweep stays disjoint |
| `AngularBudget.lean` | `OpenArc` witnesses and the Haar-measure budget |
| `ArcMetric.lean` | Midpoint separation of disjoint arcs; circle perimeter inequality; three-arc budget |
| `Charts.lean` | `SquareChart`: membership in a square's own phase, sorted coordinates, arcs from chart intervals |
| `Coordinates.lean` | Points in a rotated frame; Cartesian chart membership; inscribed disks |
| `Regions.lean` | Disjoint regions, with the containing square replaced by its sweep; the budget for four and five squares |
| `ElementaryTrig.lean` | Arcsine and cosine estimates with exact rational constants |
| `RectangleArcs.lean` | Occupied arcs of an exterior square: the interval between its edges, and the clipped cap on small circles |
| `Constructions.lean` | Axis-parallel squares centred at given points: disjointness and containment |
| `NormalForm.lean` | Normal forms from square-by-square representations, the rigid-motion witness |
| `Angles.lean` | Quarter turns of a frame; four directions a quarter turn apart (uniqueness only) |
| `Contacts.lean` | Disjoint squares have centres at least 1 apart; equality means side-neighbours |

## The cases

| File | One | Two | Three | Four | Five |
| --- | --- | --- | --- | --- | --- |
| `Construction.lean` | the centred square | the 2×1 rectangle | the T | the 2×2 block | the plus |
| `Tangents.lean` | | | the 16-gon | the diamond | the 12-gon |
| `Exterior.lean` | | | caps of at least `120°` and their contact types; some square contains `o` | arcs of at least `90°` at radius `1/2` | arcs over `72°` |
| `Containing.lean` | | | deficit, compensation, overlap point | the sweep covers a quarter circle | the sweep covers a `72°` arc |
| `Optimality.lean` | half-diagonal bound | centre-distance bound | strict 16-gon infeasibility | strict diamond infeasibility in the disk | a square centred at `o`; strict 12-gon infeasibility |
| `Uniqueness.lean` | centred at `o` | edge to edge, `o` the midpoint | no square contains `o`; the T | `o` a vertex of every square | closed 12-gon rigidity |

Each `Construction.lean` also defines the case's `radius`, its `centers` (the
optimal packing in the frame of its disk centre) and its `model`, the
axis-parallel squares at those centres.
