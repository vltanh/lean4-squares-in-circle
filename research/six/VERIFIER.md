# n=6 reduced verifier

scripts/n6_reduced_verify.py is a diagnostic branch-and-bound driver for the
current normalized six-square state space.

## Important trust boundary

It is **not yet a proof certificate**.

The code uses ordinary IEEE-754 sin/cos evaluations, expanded by one ULP, to
guide subdivision and identify surviving branches. This is appropriate for
search and certificate discovery, but a final computer-assisted proof should
either:

1. replace the trigonometric bounds by rigorous rational/MPFI interval bounds
   and emit a replayable certificate, or
2. export the surviving finite certificate to Lean and prove the box
   exclusions there.

No search result from this script should be cited as the unrestricted n=6
proof until one of those steps is completed.

## State space

The global analytical reduction fixes one containing square C and five
exterior squares in cyclic order

    E, N, W, D, S.

The script uses 17 real coordinates:

    C_x, C_y,
    (phi_i, a_i, b_i) for i = E,N,W,D,S.

For an exterior square,

    center = a_i e(phi_i) + b_i J e(phi_i).

The initial global bounds are

    |C_x|, |C_y| <= 23/200
    177/200 <= a_i <= 223/200
    |b_i| <= 117/250

with each phi_i restricted to its primary-direction quadrant.

## Encoded analytical contractions

The current driver uses:

* exact candidate-radius containment formula
  (a+1/2)^2 + (|b|+1/2)^2;
* the five fixed open pins on the radius-9/10 auxiliary circle;
* the E/N versus southwest-foot classification;
* the simplified marker phi + 5 b / 4;
* consecutive marker gaps in [pi/3, 2pi/3];
* the 32 choices of central separator type (cardinal or own-primary);
* separating-axis overlap rejection for all ten outer-square pairs;
* the already-proved local, one-oblique-pair, and four-side/small-angle
  terminal branches.

research/six/PROGRESS.md records the mathematical provenance and limitations
of each reduction.

## Branch encoding

Bits are ordered

    E N W D S
    0 1 2 3 4

where bit 1 means that square uses its own primary edge normal as the
separator from the containing square, and bit 0 means the corresponding
cardinal normal.

The candidate branch is

    01000 (binary) = 8,

because only D uses its own primary normal.

## Usage

Quick diagnostic run:

    python scripts/n6_reduced_verify.py --branch 8 --max-nodes 100000

All 32 discrete branches:

    python scripts/n6_reduced_verify.py --branch all --max-nodes 1000000

Checkpoint one branch:

    python scripts/n6_reduced_verify.py \
      --branch 8 \
      --max-nodes 5000000 \
      --checkpoint /tmp/n6-branch8.json.gz \
      --checkpoint-every 100000

Resume:

    python scripts/n6_reduced_verify.py \
      --branch 8 \
      --resume /tmp/n6-branch8.json.gz \
      --checkpoint /tmp/n6-branch8.json.gz \
      --max-nodes 10000000

Write unresolved depth-limit boxes:

    python scripts/n6_reduced_verify.py \
      --branch 8 \
      --max-depth 56 \
      --survivors /tmp/n6-survivors.jsonl

## Current validation

Before upload, the script was syntax-checked with Python and run for a small
test tree on branch 8. That only checks basic execution; it is not evidence of
mathematical coverage.

The next implementation target is to replace the diagnostic trig interval
routine with an independently checkable enclosure and to add branch-specific
dual certificates for the small set of surviving boxes.
