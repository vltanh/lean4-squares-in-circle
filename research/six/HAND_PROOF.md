# n=6 hand-proof program

## Goal

Replace the remaining high-dimensional interval search by a small number of explicit
completed-square stress lemmas, proved by elementary monotonicity/concavity and a
handful of rational Taylor endpoint checks.

This note records only statements that have either been proved analytically below or
reduced to explicitly listed scalar inequalities. It is not yet the unrestricted n=6
proof.

## 1. Why the old verifier was slow

The 17-variable verifier repeatedly subdivides center coordinates even though the
completed-square stress identities already eliminate all centers once the separating
axes are fixed. The exact replay scripts then subdivide smooth four- or five-angle
functions thousands of times even when their true minima are simple boundary points.

The correct hierarchy is:

1. global geometry -> a small finite list of separator graphs;
2. for each graph, eliminate all centers;
3. simplify the resulting trigonometric stress symbolically;
4. prove its minimum by monotonicity/concavity;
5. use rational Taylor bounds only for final scalar endpoint inequalities.

The first worked example below reduces a former 5,110-leaf exact replay to eight
scalar inequalities.

## 2. Alternate D--W branch: source W, difficult half

Consider the exact certificate in \`check_alt_dw_certificate.py\`. Its angle domain is

\[
 |\theta_N|\le 1/6,\qquad |\theta_W|\le 2/5,\qquad
 1/6\le\theta_S\le1/2,\qquad |\epsilon|\le1/6.
\]

We treat the harder half in which the W--N separator is sourced by W and
\(\theta_W\ge0\). The other half has a much larger numerical margin; the source-N
case is analogous and is being simplified separately.

Write
\[
 a=1/6,\qquad b=2/5,\qquad h=1/\sqrt2
\]
and
\[
\begin{aligned}
 A&={41697h\over23000},&
 B&={7749h\over23000},\\
 C&={78993h\over93200},&
 E&={167031h\over466000},\\
 P&={38909\over31000},&
 Q&={949\over1000},\\
 R&={277\over1000},&
 T&={262873\over562000},\\
 K&={980542331731\over840280482000}.
\end{aligned}
\]

After expanding the completed squares and using \(h^2=1/2\), the stress lower
bound on the sign chamber containing the minimizer is

\[
\begin{aligned}
F={}&A\cos(\epsilon-\theta_S)
   +B\sin(\epsilon-\theta_S)
   +C\cos(\epsilon-\theta_W)
   -E\sin(\epsilon-\theta_W)\\
 &+Q\cos\theta_N
   +R\bigl(\cos(\theta_N-\theta_W)
            -\sin(\theta_N-\theta_W)\bigr)\\
 &+P\sin\theta_S
   -T\sin\theta_W
   +Q\cos\theta_S-K ,
\end{aligned}
\]
with the obvious \(+\sin\theta_N\) / sign variant when \(\theta_N>0\).
This is exactly the function evaluated by the old interval replay; no center
coordinate remains.

### 2.1. Eliminate theta_N

For \(0\le\theta_N\le a\), direct differentiation gives a positive derivative.
A sufficient uniform bound is

\[
 Q(\cos a-\sin a)-R>0.
\tag{N+}
\]

For \(-a\le\theta_N\le0\), put \(x=-\theta_N\). The relevant part is

\[
 Q\cos x+R\{\cos(\theta_W+x)+\sin(\theta_W+x)\},
\]
which is concave in \(x\). Hence its minimum is at \(x=0\) or \(x=a\).
The endpoint difference is decreasing in \(\theta_W\), so it suffices to check

\[
 Q(\cos a-1)
 +R\{\cos(a+b)+\sin(a+b)-\cos b-\sin b\}>0.
\tag{N-}
\]

Thus the stress is minimized at

\[
\boxed{\theta_N=0}.
\]

### 2.2. Eliminate epsilon

With \(\theta_N=0\), the epsilon-dependent part is

\[
H(\epsilon)=
 A\cos(\epsilon-\theta_S)+B\sin(\epsilon-\theta_S)
 +C\cos(\epsilon-\theta_W)-E\sin(\epsilon-\theta_W).
\]

Throughout the domain,

\[
H(\epsilon)>0,
\]
for example from the stronger scalar estimate

\[
A\cos(2/3)-B\sin(2/3)
 +C\cos(17/30)-E\sin(17/30)>0.
\tag{Econc}
\]

Therefore \(H''=-H<0\), so \(H\) is concave and its minimum is at one of
\(\epsilon=\pm a\).

Moreover
\[
H(a)-H(-a)
=2\sin a\,
 \bigl(A\sin\theta_S+B\cos\theta_S
       +C\sin\theta_W-E\cos\theta_W\bigr).
\]
The bracket is increasing separately in \(\theta_S\) and \(\theta_W\), so its
minimum is at \((a,0)\). It is positive by

\[
A\sin a+B\cos a-E>0.
\tag{Eend}
\]

Hence

\[
\boxed{\epsilon=-a}.
\]

### 2.3. Eliminate theta_W

After \(\epsilon=-a\), the W-dependent part is

\[
f_W(w)=
 R\cos w+(R-T)\sin w
 +C\cos(a+w)+E\sin(a+w),
\qquad 0\le w\le b.
\]

Its second derivative has the uniform upper bound

\[
f_W''(w)
\le -R\cos b+(T-R)\sin b-C\cos(a+b)<0.
\tag{Wconc}
\]

Thus \(f_W'\) is decreasing. At zero,

\[
f_W'(0)=R-T-C\sin a+E\cos a<0.
\tag{W0}
\]

Therefore \(f_W\) is strictly decreasing and

\[
\boxed{\theta_W=b=2/5}.
\]

### 2.4. Eliminate theta_S

The remaining S-dependent part is

\[
f_S(s)=
 A\cos(a+s)-B\sin(a+s)+P\sin s+Q\cos s,
\qquad a\le s\le1/2.
\]

It is concave, since

\[
f_S''(s)
\le -A\cos(a+1/2)+B\sin(a+1/2)-Q\cos(1/2)<0.
\tag{Sconc}
\]

Thus its minimum is at an endpoint. The endpoint comparison

\[
f_S(1/2)-f_S(a)>0
\tag{Send}
\]
shows that

\[
\boxed{\theta_S=a=1/6}.
\]

### 2.5. Final scalar margin

Consequently the entire four-angle region is minimized at

\[
(\theta_N,\theta_W,\theta_S,\epsilon)
=(0,2/5,1/6,-1/6).
\]

At this point the stress equals

\[
\begin{aligned}
F_{\min}={}&
 A\cos(1/3)-B\sin(1/3)
 +C\cos(17/30)+E\sin(17/30)\\
&+Q+R(\cos(2/5)+\sin(2/5))
 +P\sin(1/6)-T\sin(2/5)+Q\cos(1/6)-K .
\end{aligned}
\]

Exact rational Taylor bounds give

\[
F_{\min}-{142559\over50000}>0.030936815.
\tag{Final}
\]

Hence this entire alternate-axis region has a large strict radius margin.

The script \`check_alt_dw_hand.py\` verifies only the eight scalar inequalities
(N+), (N-), (Econc), (Eend), (Wconc), (W0), (Sconc), (Send), and (Final), using
\`fractions.Fraction\` and alternating Taylor bounds. It does not subdivide any
multidimensional box.

## 3. Consequence for proof architecture

This worked example shows that the exact replay scripts are overkill as final
proofs. Their interval trees should be treated only as discovery tools.

The intended replacement is:

* \`check_alt_dw_certificate.py\`: replace thousands of leaves by the argument above;
* \`check_alt_ds_d_certificate.py\`: simplify its four-angle stress similarly;
* \`check_large_candidate_graph_certificate.py\`: simplify the five-cycle stress;
* candidate equality neighborhood: use the already-proved full-dimensional local
  rigidity theorem;
* global case split: by the finite separator graph, not by center boxes.

The remaining difficult part is global graph coverage, not the scalar analysis of the
known survivor stresses.

## 4. Current structural lessons

Several tempting shortcuts have been tested and rejected:

* a single sharper pairwise marker-gap theorem is false/too weak; the central square
  and the full cycle genuinely matter;
* a single auxiliary inner-circle arc budget is too weak;
* own-primary central separation can approach cardinal separation continuously, so
  there is no uniform angle gap separating the branch types;
* straightening arbitrary helpers does not preserve every oblique separator.

The robust ingredients are instead:

1. exact cap-depth bounds for cardinal helpers;
2. the forced outer cyclic order \(E,N,W,D,S\);
3. separating-axis completeness;
4. completed-square/self-stress identities;
5. local rigidity at the unique equality configuration.

That is the route being pursued from here.


## 5. Both D--W and D--S on D-secondary: one common base stress

The second exact replay script, \`check_alt_ds_d_certificate.py\`, originally
subdivided four separate W--N source-axis cases. Its full angle domain is

\[
|\theta_N|,|\theta_W|\le1/5,\qquad
1/6\le\theta_S\le1/2,\qquad
|\epsilon|\le1/6.
\]

A symbolic expansion shows that all four source cases dominate one common
base function

\[
\begin{aligned}
B(n,w,s,e)={}&
 -b\sin(e-w)+r\cos n+r\cos s-r\cos w\\
&-j\cos(e+\pi/4)
 +A\cos(e-s)+C\cos(e-w)\\
&+u\cos(n-w)-{1071\over800},
\end{aligned}
\tag{B}
\]

where

\[
b={43\sqrt2\over1200},\quad
r={3\over50},\quad
j={17\over160},\quad
A={17\sqrt2\over10},\quad
C={2107\sqrt2\over1200},\quad
u={1\over25}.
\]

Put

\[
a={1\over6},\qquad c={1\over5},\qquad d=a+c={11\over30}.
\]

For fixed \(w\), the \(n\)-part
\[
g(n)=r\cos n+u\cos(n-w)
\]
is concave. Thus its minimum is at \(n=\pm c\); for \(w\ge0\),
\[
g(-c)-g(c)=-2u\sin c\sin w\le0,
\]
so \(n=-c\).

The \(e\)-dependent part is concave because
\[
b\sin d+j-A\cos(2/3)-C\cos d<0.
\]
For \(w\ge0\), the endpoint difference has sign
\[
-b\cos w+j/\sqrt2+A\sin s+C\sin w,
\]
which is increasing in \(s,w\) and is positive already at \((s,w)=(a,0)\):
\[
-b+j/\sqrt2+A\sin a>0.
\]
Hence \(e=-a\).

Then the \(s\)-derivative is
\[
-r\sin s-A\sin(a+s)<0,
\]
so \(s=1/2\). Finally,
\[
{dB\over dw}\le r\sin c+b-C\sin a<0,
\]
hence \(w=c\).

Therefore the \(w\ge0\) half-domain is minimized at
\[
\boxed{(n,w,s,e)=(-1/5,1/5,1/2,-1/6)}.
\]

For \(w\le0\), write \(x=-w\). The same \(n\)-concavity gives \(n=c\).
The \(e\)-part is concave, so \(e=\pm a\); for either endpoint the
\(s\)-derivative is negative, so \(s=1/2\). For each fixed \(e\), the remaining
function of \(x\) is concave; the crude positive lower bound
\[
C\cos d-b\sin d-r>0
\]
is already enough to prove this. Hence only four scalar endpoint pairs
\[
(e,x)\in\{(-a,0),(-a,c),(a,0),(a,c)\}
\]
remain. All four are above the preceding hard corner; the smallest excess is
greater than \(0.122\).

At the hard corner,
\[
\begin{aligned}
B_{\min}={}&
 b\sin d+r\cos(1/2)
 -j{(\cos a+\sin a)\over\sqrt2}\\
&+A\cos(a+1/2)+C\cos d+u\cos(2c)-{1071\over800}.
\end{aligned}
\]
Exact Taylor bounds give
\[
B_{\min}-{142559\over50000}>0.038647324.
\]

The other three W--N source-axis formulas differ from this common base by
small explicitly bounded terms. Uniform lower corrections are

\[
L_{Wp}={1\over25}+r(\cos c-\sin c)-2b,
\]
\[
L_{Np}={1\over25}+r\cos c-2b(\sin d+\cos d),
\]
\[
L_{Ns}=-r+r\cos c-2b\sin d.
\]

After these worst-case corrections the remaining squared-radius margins are

\[
B_{\min}-Q_0+L_{Wp}>0.02417918,
\]
\[
B_{\min}-Q_0+L_{Np}>0.00650120,
\]
\[
B_{\min}-Q_0+L_{Ns}>0.00111606.
\]

Thus all four source-axis cases in this second alternate-D family are excluded
by one hand minimization and three scalar comparisons.

The script \`check_alt_ds_d_hand.py\` verifies only these scalar signs and
endpoint comparisons; it performs no multidimensional subdivision.

## 6. Updated computational role

Two formerly expensive exact replay families are now reduced to short analytic
lemmas:

1. alternate D--W secondary axis;
2. both D--W and D--S on D-secondary.

The computer is now used only for fixed rational/Taylor arithmetic at a few
scalar endpoints. The next target is the large-angle candidate contact graph,
whose five-angle replay should be simplified in the same way.


## 7. Large-angle candidate contact graph: concavity replaces 5D replay

The third exact replay family is
\`check_large_candidate_graph_certificate.py\`. Its domain is

\[
1/6\le\theta_E,\theta_N,\theta_W,\theta_S\le1/3,
\qquad
|\epsilon_D|\le1/4,
\]

with four possible source-axis choices for the mixed \(W\!-\!N\) and
\(S\!-\!E\) separators.

The only nonsmoothness comes from the signs of

\[
\theta_N-\theta_W,\qquad
\theta_E-\theta_S.
\]

Hence there are four smooth sign chambers.

### 7.1. Uniform separate concavity

On every source choice and every sign chamber, the stress is strictly concave
in each individual variable.  A coarse source-independent proof uses the
following positive curvature contributions.

Put \(a=1/6\), \(b=1/3\).  Lower bounds for the unary curvature magnitudes are

\[
T_E=
\min\left\{
{167\over500}\cos b,\,
{6847\over35000}\sin a+{26263\over140500}\cos b
\right\},
\]

\[
T_N=
\min\left\{
{84\over125}(\sin a+\cos b),\,
{1848\over6625}\sin a+{12043\over25625}\cos b
\right\},
\]

\[
T_S=
\min\left\{
{8003927\over9835000}\sin a+{18438\over35125}\cos b,\,
{21714\over35125}\sin a+{84\over125}\cos b
\right\},
\]

\[
T_W=
\min\left\{
{13527\over102500}\cos b-{498416\over1358125}\sin b,\,
{668\over25625}\sin a+{167\over500}\cos b
\right\}.
\]

The common pair-curvature bounds are

\[
D_{DW}={189\sqrt2\over500}\cos(7/12),
\]

\[
D_{NW}={31\over125}\bigl(\cos a-\sin a\bigr),
\]

\[
D_{DS}={517\over1000\sqrt2}
\bigl(\cos(1/12)-\sin(1/12)\bigr),
\]

while the only potentially wrong-sign pair term contributes at most

\[
P={97713\over197000}\sin a.
\]

These give the following strictly positive margins:

\[
T_E>0.20909,\qquad
T_N>0.49037,
\]

\[
T_W+D_{DW}+D_{NW}-P>0.57193,
\]

\[
T_S+D_{DS}-P>0.88263,
\]

\[
D_{DW}+D_{DS}>0.78004.
\]

Therefore the second derivative in each of the five coordinates is strictly
negative on every chamber.

### 7.2. Concavity on the two chamber diagonals

To reduce an ordered pair triangle to its vertices, separate concavity alone is
not quite enough: one must also control the equality boundary.

Along \(\theta_N=\theta_W\), the \(N-W\) relative-angle term is constant.  A
uniform lower curvature margin is

\[
T_N+T_W+D_{DW}-P>0.85889.
\]

Along \(\theta_E=\theta_S\), the \(E-S\) relative-angle term is constant and

\[
T_E+T_S+D_{DS}-P>1.09172.
\]

Thus both equality diagonals are strictly concave as one-variable functions.

### 7.3. Chamber minima are vertices

For a chamber \(\theta_N\ge\theta_W\), fix \(\theta_W\). Concavity in
\(\theta_N\) sends the minimum to either
\(\theta_N=\theta_W\) or \(\theta_N=1/3\).  On the second edge, concavity in
\(\theta_W\) sends the minimum to an endpoint; on the equality edge, diagonal
concavity does the same.  Therefore the \((\theta_N,\theta_W)\) triangle has
its minimum at its three vertices.

The same argument applies to the opposite \(N/W\) chamber and to both \(E/S\)
chambers.  Finally the stress is concave in \(\epsilon_D\), so its minimum is
at \(\epsilon_D=\pm1/4\).

Taking the union of the four chambers, every possible minimum is therefore
among

\[
(\theta_N,\theta_W)\in\{1/6,1/3\}^2,
\qquad
(\theta_E,\theta_S)\in\{1/6,1/3\}^2,
\qquad
\epsilon_D\in\{-1/4,1/4\}.
\]

That is only \(4\cdot4\cdot2=32\) angle vertices per source-axis choice, or
128 fixed evaluations total.

### 7.4. Endpoint margin

The exact point-evaluation checker finds the same worst vertex for all four
source-axis choices:

\[
\boxed{
\theta_E=\theta_N=\theta_W=\theta_S=1/6,\qquad
\epsilon_D=1/4.
}
\]

At that vertex,

\[
F-Q_0>0.01834164.
\]

Thus the former five-dimensional replay tree for this entire large-angle
family reduces to:

1. seven uniform scalar concavity inequalities;
2. 128 fixed endpoint evaluations.

The companion script \`check_large_hand.py\` performs exactly those checks and
contains no recursive subdivision.

## 8. Status after the three hand reductions

All three existing nonlocal exact replay families now have hand-proof
reductions:

1. alternate \(D-W\) secondary axis: monotonicity/concavity, one final corner;
2. both \(D-W,D-S\) on \(D\)-secondary: one base stress plus source corrections;
3. large-angle candidate graph: chamber concavity plus 128 endpoint values.

The remaining issue is no longer the analytic complexity of these stresses.
It is proving that the global normalized packing falls into the union of these
graph families, the already-proved local-rigidity region, or another similarly
simple graph family.
