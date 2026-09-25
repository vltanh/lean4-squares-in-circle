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
