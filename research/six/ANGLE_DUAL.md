# n=6 angle-only contact-graph dual

## Purpose

The 17-variable branch-and-bound search is useful diagnostically, but it is not
the intended final closure mechanism.  The centers can be eliminated
analytically once a separating-axis graph is fixed.

This note records the reduced dual that remains after that elimination.

## Fixed discrete data

Normalize the containing square (C) to angle (0).  For the five exterior
squares use the already established cyclic order

[
E,N,W,D,S.
]

A discrete branch consists of

1. one of the canonical central-separator patterns, and
2. one separating source axis for each of

[
W!-!N,qquad S!-!E,qquad D!-!W,qquad D!-!S.
]

For fixed square angles, each selected separator gives a directed inequality

[
n_ecdot(p_{j(e)}-p_{i(e)})ge H_e,
]

where (H_e) is the sum of the two square support radii in direction (n_e).

The only continuous geometric variables retained by the final certificate are
the five square angles.

## Eliminate all centers

For square (i), choose any one of its four vertices (m_i) relative to its
center.  Thus

[
|m_i|^2=rac12.
]

Let (lambda_ige0), (sum_ilambda_i=1), be containment weights.  Let
(mu_ege0) be separator multipliers and define the force on square (i) by

[
G_i=
sum_{e:j(e)=i}mu_e n_e-
sum_{e:i(e)=i}mu_e n_e.
]

Weighted vertex containment gives

[
R^2gesum_ilambda_i|p_i+m_i|^2.
]

Using the selected separator inequalities and completing squares,

[
R^2ge
rac12+sum_emu_eH_e
-sum_irac{|2lambda_i m_i-G_i|^2}{4lambda_i}.
	ag{1}
]

Expand the last term.  Since (|m_i|^2=1/2) and
(sum_ilambda_i=1), the two constant halves cancel.  Put

[
A(mu)=sum_emu_eH_e+sum_i m_icdot G_i.
]

Then (1) becomes

[
R^2ge
A(mu)-sum_irac{|G_i|^2}{4lambda_i}.
	ag{2}
]

For fixed (mu), Cauchy--Schwarz minimizes the last sum over the
(lambda_i):

[
min_{lambda_ige0, sumlambda_i=1}
sum_irac{|G_i|^2}{lambda_i}
=
left(sum_i|G_i|ight)^2.
]

Consequently every fixed contact graph has the angle-only lower bound

[
oxed{
R^2ge
A(mu)-rac14
left(sum_i|G_i|ight)^2.
}
	ag{3}
]

No center coordinate occurs in (3).

## Eliminate the multiplier scale

Write (mu=t
u), (tge0), and define

[
A_
u=A(
u),qquad
C_
u=sum_i|G_i(
u)|.
]

Equation (3) is

[
R^2ge tA_
u-rac{t^2C_
u^2}{4}.
]

If (A_
u>0), optimizing the scalar (t) gives

[
oxed{
R^2geleft(rac{A_
u}{C_
u}ight)^2.
}
	ag{4}
]

Thus certificate discovery for a fixed angle tuple is the convex problem

[
	ext{maximize }A_
u
quad	ext{subject to}quad

u_ege0,quad
sum_i|G_i(
u)|le1.
]

This is an SOCP-type problem with only the separator multipliers as unknowns.
For the present stress graph there are nine multipliers: five central edges
and four outer edges.

## Exact replay condition

For an angle box, take a rational nonnegative vector (
u).  Exact Taylor
intervals provide

[
A_
uge A_{m lo}>0
]

and an upper bound

[
C_
ule C_{m hi}.
]

To rule out (R^2le Q_0=142559/50000), it is enough to check the purely
rational inequality

[
oxed{
A_{m lo}^2>Q_0,C_{m hi}^2.
}
	ag{5}
]

So exact replay does not need the optimized containment weights, the center
coordinates, or even the square root of (Q_0).

## Diagnostic survivor reduction

The saved depth-48 boxes from the existing diagnostic search are not a
complete cover, but they reveal a much smaller discrete problem.

Among the canonical patterns, depth-48 survivors encountered so far occur only
in

[
8, 9, 11, 15, 24, 25, 27.
]

Their encountered survivor counts are respectively

[
1263, 19, 64, 12, 2333, 6378, 305.
]

These are diagnostic counts from the saved runs, not final proof statistics.

The dominant outer-axis signatures use only a small subset of the nominal
four axes per pair:

* (W!-!N): mostly the near-horizontal source axes;
* (S!-!E): mostly the near-vertical source axes;
* (D!-!W): overwhelmingly (D)-secondary or (W)-secondary;
* (D!-!S): overwhelmingly (D)-secondary or (S)-secondary.

The two already checked exact alternate-axis certificates cover large pieces
of patterns 8 and 9.  The remaining task should therefore enumerate these
contact-graph choices directly and certify their five-angle domains with
(5), instead of continuing the 17-variable center subdivision.

## Intended final architecture

1. Use the global geometric reduction only to obtain the canonical central
   pattern and the four mandatory outer-pair SAT choices.
2. Enumerate the resulting finite contact graphs.
3. For each graph, discover one or a small number of rational multiplier
   vectors (
u).
4. Subdivide only the five-angle box until (5) holds, or an existing analytic
   theorem applies.
5. Replay all leaves with exact rational Taylor bounds.
6. Use the local rigidity theorem for the candidate neighborhood.

This is the replacement for the full 17-variable branch-and-bound search.
