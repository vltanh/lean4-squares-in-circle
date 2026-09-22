# Three unit squares in a disk: a proposed finite-certificate proof

## Statement and status

**Theorem claimed.** If three squares of side length 1, with pairwise disjoint interiors and arbitrary independent orientations, lie in a disk of radius \(R\), then
\[
R\geq R_*:=\frac{5\sqrt{17}}{16}.
\]
Equality is attainable. Equivalently, the largest possible common side length in a disk of radius 1 is \(16/(5\sqrt{17})\).

This is a proposed new proof, not a claim that an independently reviewed proof has been located. Erich Friedman's *Squares in Circles* catalogue, consulted on 21 September 2026, lists this construction but does not mark the three-square case as proved. The accompanying standard-library Python program checks all finite arithmetic certificates using exact rational numbers and rigorously bounded trigonometric series. It does not formally verify the geometric reductions; those are proved below. Independent review of the entire argument remains appropriate.

## 1. Construction

Use
\[
S_0=[-1,0]\times[-1,0],\quad
S_1=[0,1]\times[-1,0],\quad
S_2=[-\tfrac12,\tfrac12]\times[0,1].
\]
Their interiors are disjoint. The circle centered at \((0,-3/16)\) contains all three squares because the greatest squared distances of their vertices from that point are
\[
1+\left(\frac{13}{16}\right)^2
=\frac14+\left(\frac{19}{16}\right)^2
=\frac{425}{256}=R_*^2.
\]
A disk is convex, so checking the vertices is sufficient.

It remains to prove the lower bound. Put the center of an arbitrary enclosing disk at the origin and suppose \(R\leq R_*\).

## 2. Normalizing all independent orientations

A square's orientation is defined modulo \(\pi/2\). Consider the three orientations as points on a circle of circumference \(\pi/2\). Cut after a largest gap, rotate, and relabel. Their orientations can then be written as
\[
\theta_0=0,\qquad \theta_1=a,\qquad \theta_2=b.
\]
The omitted gap is \(\pi/2-b\), so it is at least both \(a\) and \(b-a\). Reflection and relabeling of the endpoints allow \(a\leq b/2\). Consequently the normalized angles lie in
\[
D=\{(a,b):0\leq a\leq b/2,\quad 2b-a\leq\pi/2\}.
\]
Conversely, the only property needed below is that every orientation triple can be put in this domain. It is the triangle with vertices
\[
O=(0,0),\qquad V=(0,\pi/4),\qquad W=(\pi/6,\pi/3).
\]
In particular,
\[
0\leq a\leq\pi/6,\quad 0\leq b\leq\pi/3,\quad
0\leq d:=b-a\leq\pi/4.
\]

Let \(U_\theta\) be rotation by angle \(\theta\). Use the ordered local vertices
\[
q_1=(-\tfrac12,-\tfrac12),\quad
q_2=(-\tfrac12,\tfrac12),\quad
q_3=(\tfrac12,-\tfrac12),\quad
q_4=(\tfrac12,\tfrac12).
\]
Square \(i\) has center \(c_i\) and vertices \(c_i+U_{\theta_i}q_j\).

## 3. A bound on the square centers

For any square with center \(c\), with orthonormal edge directions \(u,v\), the maximum squared norm of its vertices is
\[
|c|^2+\frac12+|c\cdot u|+|c\cdot v|
\geq |c|^2+|c|+\frac12.
\]
Thus, writing \(r=|c|\),
\[
(r+\tfrac12)^2+\tfrac14\leq R^2.
\]
Since \(R\leq R_*\), every center satisfies
\[
|c_i|\leq\sqrt{R_*^2-\tfrac14}-\tfrac12
=\frac{19}{16}-\frac12=\frac{11}{16}=:\rho.
\tag{1}
\]

## 4. Separating axes and a forbidden-chain lemma

Define the cardinal unit vectors
\[
e_0=(1,0),\quad e_1=(0,1),\quad e_2=(-1,0),\quad e_3=(0,-1).
\]

For every pair \(i<j\), disjoint interiors imply the existence of a separating axis normal to an edge of one of the two squares. One way to prove this standard polygon fact is to consider their Minkowski difference: its edge normals are edge normals of the two squares, and the difference of the centers is not in its interior.

Hence we can choose a source \(s_{ij}\in\{i,j\}\) and an index \(k_{ij}\in\{0,1,2,3\}\) such that, with
\[
n_{ij}=U_{\theta_{s_{ij}}}e_{k_{ij}},\qquad
h(t)=\frac{1+\cos t+\sin t}{2},
\]
we have
\[
n_{ij}\cdot(c_j-c_i)\geq h(\theta_j-\theta_i).
\tag{2}
\]
Here \(0\leq\theta_j-\theta_i\leq\pi/3\), so the displayed expression is exactly the sum of the two square half-widths in that direction. Reversing an ordered pair reverses its normal and adds 2 to its cardinal index, modulo 4.

A common rotation by a multiple of \(\pi/2\) leaves the normalized square orientations unchanged modulo \(\pi/2\). Use it to make \(k_{01}=0\).

### Forbidden-chain lemma

There cannot be a directed path \(i\to j\to k\) whose two chosen normals have the same cardinal index.

To prove this, let the angle between those normals be \(\phi\). Having the same cardinal index means that
\[
\phi=|\theta_p-\theta_q|\leq\pi/3
\]
for their respective source squares \(p\in\{i,j\}\), \(q\in\{j,k\}\). Put
\[
\delta_1=|\theta_i-\theta_j|,\qquad
\delta_2=|\theta_j-\theta_k|.
\]
The triangle inequality gives \(\delta_1+\delta_2\geq\phi\).

The function \(h\) is concave on \([0,\pi/3]\), so it lies above its endpoint chord:
\[
h(t)\geq1+\kappa t,\qquad
\kappa=\frac{3(\sqrt3-1)}{4\pi}>\frac7{44}.
\]
The last bound follows from \(\sqrt3>5/3\) and \(\pi<22/7\). Consequently (2) requires
\[
h(\delta_1)+h(\delta_2)\geq 2+\frac7{44}\phi.
\tag{3}
\]

On the other hand, adding the two separating inequalities and using (1) gives
\[
\begin{aligned}
h(\delta_1)+h(\delta_2)
&\leq -n_1\cdot c_i+(n_1-n_2)\cdot c_j+n_2\cdot c_k\\
&\leq\rho(2+|n_1-n_2|)\\
&=\frac{11}{8}\bigl(1+\sin(\phi/2)\bigr)\\
&\leq\frac{11}{8}+\frac{11}{16}\phi.
\end{aligned}
\tag{4}
\]
But the lower bound in (3) exceeds the upper bound in (4), because
\[
\frac58-\frac{93}{176}\phi
>\frac58-\frac{93}{176}\frac{22}{21}
=\frac1{14}>0.
\]
This contradiction proves the lemma.

### Exhaustive remaining patterns

Check the 16 possibilities for \((k_{02},k_{12})\), with \(k_{01}=0\), reversing normals when traversing an edge backwards. Exactly six have no forbidden chain:
\[
(0,1),\ (0,3),\ (1,1),\ (1,2),\ (3,2),\ (3,3).
\tag{5}
\]
All other patterns are excluded by the lemma.

For each of the six remaining patterns, the sources have precisely the eight possibilities
\[
(s_{01},s_{02},s_{12})\in
\{0,1\}\times\{0,2\}\times\{1,2\}.
\tag{6}
\]
It therefore suffices to handle 48 branches. The checker independently enumerates all 16 cardinal patterns and all eight source choices.

## 5. A quadratic lower-bound certificate

Fix a branch. Choose nonnegative vertex weights \(\lambda_{ij}\) and separating-inequality weights \(\mu_{01},\mu_{02},\mu_{12}\), satisfying
\[
\sum_{i,j}\lambda_{ij}=1,\qquad
w_i:=\sum_j\lambda_{ij}>0.
\]
Put
\[
m_i=\sum_j\lambda_{ij}q_j,
\]
and define the force vector
\[
f_i=\sum_{j>i}\mu_{ij}n_{ij}-\sum_{j<i}\mu_{ji}n_{ji}.
\]
The notation \(n_{ji}\) in the second sum denotes the originally chosen normal for the increasing ordered pair \(j<i\).

For any feasible configuration, the weighted disk inequalities and (2) imply
\[
R^2\geq
\sum_{i,j}\lambda_{ij}|c_i+U_{\theta_i}q_j|^2
+\sum_{i<j}\mu_{ij}\left[
h(\theta_j-\theta_i)-n_{ij}\cdot(c_j-c_i)\right].
\]
Completing squares separately in the three unconstrained center vectors yields
\[
R^2\geq F(a,b):=
\frac12+\sum_{i<j}\mu_{ij}h(\theta_j-\theta_i)
-\sum_i\frac{|U_{\theta_i}m_i+f_i/2|^2}{w_i}.
\tag{7}
\]
This lower bound is valid whether or not its unconstrained minimizing centers themselves form a packing.

### Exact coefficient formula

To make every arithmetic check reproducible, write
\[
U_{\theta_i}m_i+f_i/2=\sum_{p=0}^2 U_{\theta_p}v_{ip}.
\]
The rational vectors \(v_{ip}\) are obtained by putting \(m_i\) in \(v_{ii}\), then adding \(\mu_{ij}e_{k_{ij}}/2\) to \(v_{i,s_{ij}}\) and subtracting it from \(v_{j,s_{ij}}\), for each increasing pair \(i<j\).

Expansion of (7) gives
\[
F=C+A_a\cos a+A_b\cos b+A_d\cos d
+B_a\sin a+B_b\sin b+B_d\sin d,\quad d=b-a.
\tag{8}
\]
The coefficient for each pair \((p,q)=(0,1),(0,2),(1,2)\) corresponds respectively to \(a,b,d\), and is
\[
\begin{aligned}
C&=\frac12+\frac12\sum_e\mu_e-\sum_{i,p}\frac{|v_{ip}|^2}{w_i},\\
A_{pq}&=\frac{\mu_{pq}}2-2\sum_i\frac{v_{ip}\cdot v_{iq}}{w_i},\\
B_{pq}&=\frac{\mu_{pq}}2+2\sum_i\frac{\det(v_{ip},v_{iq})}{w_i}.
\end{aligned}
\tag{9}
\]
All seven coefficients are rational. The checker computes them directly from (9), rather than assuming precomputed coefficients.

## 6. The 48 base certificates

In the following table, each displayed vertex-weight row must be divided by 64, and each displayed separating-weight row must be divided by 512. Vertex order is \(q_1,q_2,q_3,q_4\), and separating-weight order is \(01,02,12\).

| Pattern \((k_{02},k_{12})\) | \(64\lambda_0\) | \(64\lambda_1\) | \(64\lambda_2\) | \(512\mu\) |
|---|---|---|---|---|
| \((0,1)\) | \((13,13,0,0)\) | \((0,0,19,0)\) | \((0,0,0,19)\) | \((247,247,304)\) |
| \((0,3)\) | \((13,13,0,0)\) | \((0,0,0,19)\) | \((0,0,19,0)\) | \((247,247,304)\) |
| \((1,1)\) | \((19,0,0,0)\) | \((0,0,19,0)\) | \((0,13,0,13)\) | \((304,247,247)\) |
| \((1,2)\) | \((19,0,0,0)\) | \((0,0,13,13)\) | \((0,19,0,0)\) | \((247,304,247)\) |
| \((3,2)\) | \((0,19,0,0)\) | \((0,0,13,13)\) | \((19,0,0,0)\) | \((247,304,247)\) |
| \((3,3)\) | \((0,19,0,0)\) | \((0,0,0,19)\) | \((13,0,13,0)\) | \((304,247,247)\) |

Use the row for the cardinal pattern with each of the eight source choices (6). Equation (9) then gives the 48 base functions. In every case, exact rational arithmetic gives
\[
F(O)=C+A_a+A_b+A_d=\frac{425}{256}.
\tag{10}
\]

## 7. Concavity on the entire angle domain

For a coefficient function (8), put
\[
g_a=A_a\cos a+B_a\sin a,\quad
g_b=A_b\cos b+B_b\sin b,\quad
g_d=A_d\cos d+B_d\sin d.
\]
Its negative Hessian is
\[
-\nabla^2F=
\begin{pmatrix}
g_a+g_d&-g_d\\
-g_d&g_b+g_d
\end{pmatrix}.
\tag{11}
\]

The angle ranges in Section 2 give the elementary rational bounds
\[
\cos a\geq6/7,\quad \cos b\geq1/2,\quad \cos d\geq7/10,
\]
\[
0\leq\sin a\leq1/2,\quad
0\leq\sin b\leq7/8,\quad
0\leq\sin d\leq3/4.
\]
For \(x=a,b,d\), let \(l_x=(6/7,1/2,7/10)\) and \(u_x=(1/2,7/8,3/4)\), respectively, and define
\[
t_x=
\begin{cases}A_xl_x,&A_x\geq0,\\ A_x,&A_x<0,\end{cases}
+\min(B_x,0)u_x.
\]
Then \(g_x\geq t_x\). It is sufficient for strict concavity that
\[
t_a+t_d>0,\quad t_b+t_d>0,\quad
t_at_b+t_at_d+t_bt_d>0.
\tag{12}
\]
Indeed, the corresponding matrix with \(t\)'s is positive definite, and the difference from (11) is a sum of three nonnegative multiples of rank-one positive-semidefinite matrices.

For every base certificate and every supplementary certificate below, the exact rational checks establish the stronger inequalities
\[
t_a+t_d>\frac13,\qquad
t_b+t_d>\frac3{16},\qquad
t_at_b+t_at_d+t_bt_d>\frac3{40}.
\tag{13}
\]
Thus all 53 functions used are strictly concave throughout \(D\).

A concave function on a convex polygon is at least the minimum of its values at the polygon's vertices. Accordingly, only finitely many vertex evaluations remain.

## 8. Five exceptional branches and their supplements

For 43 of the 48 branches, the base function satisfies
\[
F(V)>425/256+1/250,\qquad
F(W)>425/256+1/250.
\]
Together with (10) and concavity, this proves \(F\geq425/256\) throughout \(D\) in those branches.

The five exceptions are listed below. Set
\[
P=V/2=(0,\pi/8),\qquad Z=W/2=(\pi/12,\pi/6).
\]
The notation \([X,Y,Z]\) means the convex hull of the listed points; four listed points similarly designate a convex quadrilateral.

| Pattern | Sources \((s_{01},s_{02},s_{12})\) | Region using the base function | Region using a supplement |
|---|---|---|---|
| \((0,3)\) | \((1,0,1)\) | \([O,V,Z]\) | \([V,W,Z]\), use \(G\) |
| \((1,1)\) | \((0,0,2)\) | \([O,P,W]\) | \([P,V,W]\), use \(H\) |
| \((1,1)\) | \((1,0,2)\) | \([O,P,W]\) | \([P,V,W]\), use \(H\) |
| \((3,3)\) | \((0,2,1)\) | \([O,P,W]\) | \([P,V,W]\), use \(J\) |
| \((3,3)\) | \((1,2,1)\) | \([O,P,Z]\) | \([P,V,W,Z]\), use \(J\) |

Each row's two regions cover \(D\), with disjoint interiors.

Here are the supplementary weights, with no scaling factors. An expression such as \(3q_1/10\) in a square's column means weight \(3/10\) on vertex \(q_1\), and zero on its other vertices; it does not mean a new vertex.

| Supplement | Weighted vertex of square 0 | Weighted vertex of square 1 | Weighted vertex of square 2 | \((\mu_{01},\mu_{02},\mu_{12})\) |
|---|---|---|---|---|
| \(G\) | \(3q_1/10\) | \(2q_4/5\) | \(3q_1/10\) | \((4/5,0,4/5)\) |
| \(H\) | \(5q_1/16\) | \(5q_3/16\) | \(3q_4/8\) | \((1/2,11/16,3/8)\) |
| \(J\) | \(5q_2/16\) | \(5q_4/16\) | \(3q_1/8\) | \((1/2,3/8,11/16)\) |

Use the indicated weights with the sources of the branch being checked. For example, the supplement in the first row expands particularly simply:
\[
G(a,b)=-\frac4{15}+\frac45
\left(\cos a+\sin a+\cos(b-a)+\sin(b-a)\right).
\]

For every region in the exception table, its designated function has value exactly \(425/256\) at \(O\) when \(O\) is present, and value greater than \(425/256+1/250\) at every other listed vertex. Its concavity proves the required lower bound on the entire region.

## 9. What the exact checker verifies

The file `three_squares_circle_certificate.py` uses only the Python standard library. Run it without optimization flags:

```sh
python three_squares_circle_certificate.py
```

The checker enumerates all cardinal/source cases, validates the nonnegative weights and their normalization, generates (9) with `fractions.Fraction`, checks the rational concavity inequalities (13), verifies that each one- or two-piece polygon cover is exact, and evaluates the designated functions at all 160 polygon vertices.

Trigonometric values are enclosed rigorously, not rounded and compared with a tolerance. The checker first bounds
\[
\pi=16\arctan(1/5)-4\arctan(1/239)
\]
by rational alternating-series bounds. It then bounds sine and cosine by their alternating Taylor series, using monotonicity to handle the rational interval for \(\pi\). Every argument is between 0 and \(\pi/3\); the series terms decrease in magnitude. All resulting comparisons are comparisons of rational numbers. Assertions cannot silently be disabled: running with `-O` is explicitly rejected.

The checker has been executed and returns:

```text
PASS: all 16 cardinal patterns checked; 10 excluded by the chain lemma.
PASS: all 48 remaining source/direction branches covered.
PASS: 53 valid dual certificates have strictly concave angle functions.
PASS: all angle-domain polygon covers checked using rational arithmetic.
PASS: every tested nonzero vertex has F - 425/256 > 1/250.
PASS: at the zero-angle vertex, every base certificate equals 425/256.
PASS: trigonometric evaluations use rational alternating-series bounds.
Certificate/vertex checks: 53/160.
```

The program checks finite arithmetic claims, not a floating-point search over configurations. Its source contains the complete certificate data.

## 10. Conclusion

Suppose three interior-disjoint unit squares fit in a disk with \(R<R_*\). Normalize their orientations as in Section 2 and choose separating axes as in Section 4.

If the cardinal pattern is not in (5), the forbidden-chain lemma gives a contradiction. Otherwise, it is one of the 48 remaining branches. Sections 5–9 provide a valid certificate function at its angle point with
\[
R^2\geq F(a,b)\geq\frac{425}{256}=R_*^2,
\]
again a contradiction.

Thus \(R\geq R_*\) for every packing, including those with independently rotated squares. The construction in Section 1 attains \(R_*\), giving the claimed optimum:
\[
\boxed{R_{\min}=\frac{5\sqrt{17}}{16}}.
\]

The certificates also force \(a=b=0\) in any equality case: away from \(O\), their concavity and the strict vertex inequalities give \(F>425/256\). Thus equality requires the three square orientations to agree modulo \(\pi/2\).
