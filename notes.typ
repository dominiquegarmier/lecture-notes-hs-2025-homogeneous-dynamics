#import "template/preamble.typ": *

#show: lecture_notes.with(
  lecture: [Homogeneous Dynamics],
  lecture_id: [401-3375-67L],
  lecturer: [Manfred Einsiedler],
  authors: (
    (
      name: "Dominique Garmier",
      affiliation: "ETH Zurich",
      email: "dgarmier@ethz.ch",
    ),
  ),
  semester: [Fall 2025],
)

#let link_box(
  doc,
) = box(
  stroke: 0.1pt,
  outset: 1pt,
  doc,
)

#show link: link_box

= Introduction

This lecture has as a goal to finish a long ongoing project @ew2011.

== Interactions

In this lecture we will interact with the following domains of mathematics:

- Dynamical systems
- Ergodic Theory
- Functional Analysis
- Algebraic Number Theory
- Analytic Number Theory
- Diophantine Problems, incl. Diopahntine Approximation
- Lie Groups
- Geometry
- Algebraic Geometry & algebraic groups
- Distribution Problems (e.g. $sqrt(n) mod 1$ gaps,
  frobenius numbers, integer points on spheres, values of quadratic forms)

= Lattices & The space of Lattices

== Review on $"SL"_2(ZZ) backslash "SL"_2(RR)$

Consider $HH = {z in CC | im z > 0}$.
Using the Riemannian metric
$
  dif s^2 = (dif x^2 + dif y^2) / y^2,
$

*Mobius transformations*::
Consider $g in "PSL"_2(RR) = "SL"_2(RR) slash {plus.minus I}$ acting on $HH$ by
$
  z in HH |-> g dot z = (a z + b) / (c z + d).
$
#remark[
  It is easy to check that the above action with $"SL"_2(RR)$ is indeed a group action. Noticing that $plus.minus id$ acts trivially we get that the above
  is indeed a group action aswell.
]

#remark[
  One can check that the Mobis transformations are isometric of $HH$. I.e.
  they preserve the hyperbolic metric.
]

We have in particular that:
$
  im(g dot z) = (im z) / (|c z + d|^2).
$

Notice that
$
  mat(1, s; ,1): z |-> z + s,\
  mat(, -1; 1, ): z |-> -1 / z.
$

Consider now the groups
$
  B = {mat(e^(-t slash 2), s; , e^(t slash 2)) | s in RR, t in RR}
  subset "SL"_2(RR),
$
called the borel subgroup.
$
  B = A N
$
for
$
  A = {mat(e^(-t slash 2), ; , e^(t slash 2)) | t in RR},
$
called the diagonal or cartan subgroup, and
$
  N = {mat(1, s; ,1) | s in RR},
$
called the unipotent subgroup.

Notice we can now see that $B$ acts transitively on $HH$.
However $"SL"_2(RR)$ does not act faithfully on $HH$. Indeed
$
  K = "SO"_2(RR)
$
fixes $i in HH$. Infact $K$ is the stabilizer of $i$ in $"SL"_2(RR)$.

We will now construct an action on the tangent bundle $T HH$. Or more precisely
the unit tangent bundle $T^1 HH$.

#remark[
  Note that the unit tangent bundle is the set
  $
    T^1 HH = {(z, v) in HH times CC | |v|_z = 1},
  $
  where
  $
    |v|_z = (|v|) / im(z).
  $
  I.e. "unit" refers to the hyperbolic metric.
]

The (complex) derivative of the Mobius transformation for $g in "PSL"_2(RR)$
acts transitively on $T^1 HH$. Indeed it is simply transitive.

Thus we have
$
  T^1 HH isom "PSL"_2(RR).
$
say using $(i, arrow.t)$ as the the vector pointing up at $i$.

On $T^1 HH$ there is a geodesic flow $g_t$ given by
simply following the geodesic determined by tangency
by $(z, v) in T^1 HH$ at unit speed for time $t$.

For $(i, arrow.t)$ the geodesic orbit is
$
  (e^t i, e^t arrow.t)
$
Now by applying the derivative of the Mobius transformation
we can get all geodesic orbits.

Indeed
$
  (D g) (e^t i, e^t arrow.t)
$
is the geodesic orbit starting at $D g (i, arrow.t)$.

*Claim*:
The geodesic flow corresponds to right multiplication by
$
  a_t = mat(e^(t slash 2), ; , e^(-t slash 2)).
$
for $t in RR$.

#proofidea[of Claim][
  1. we show that the claim holds for $(i, arrow.t)$, this is a straightforward
    computation.

  2. The claim is true for all $(z, v)$ since left and right
    multiplication commutes.
]

While left-multiplication by any $g in "PSL"_2(RR)$ corresponds to (the dirative of) the mobius transformation.

Right multiplication by $K$ fixes basepoints and rotates vectors. Right multiplication by
$
  N = U = U^- = {mat(1, s; ,1) | s in RR}
$
creates stable horocycles, while right multiplication by
$
  U^+ = {mat(1, ; s, 1) | s in RR}
$
creates unstable horocycles.

#remark[
  Horocycles are curves which are everywhere perpendicular to the geodesics.
]

#remark[
  Look at stable and unstable manifolds of the geodesic flow.
  - stable or unstable manifolds, are submanifolds that when
    following geodesics either move together in the future or
    appart in the future.
]

To get an interesting dynamics we need to "fold up" the space $T^1 HH$.
We can do this by a discrete subgroup of isometries
$"Isom"(T^1 HH)^0 = "PSL"_2(RR)$. Our example is
$
  Gamma := "PSL"_2(ZZ).
$

We now consider
$
  X_2 := Gamma backslash "PSL"_2(RR) = "SL"_2(ZZ) backslash "SL"_2(RR).
$
which is sometimes called an "orbifold". Right multiplications still have the
same meaning (since the quotient is on the left).

#bibliography("bib.bib", full: true)
