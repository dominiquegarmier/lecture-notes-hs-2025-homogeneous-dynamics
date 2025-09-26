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
which is sometimes called an "orbifold" (manifold with holes). Right multiplications still have the
same meaning (since the quotient is on the left).

=== Remarks About Notation

We write $G acts X$ for a group action of $G$ on $X$. Given a group action
we write $G x$ for the orbit of $x in X$. And we denote by $"Stab"_G(x)$ the
subgroup of $G$ that fixes $x$.

With this we get

#theorem[Stabilizer-Orbit-Theorem][
  $
    G slash "Stab"_G(x) &isom G x,\
    g "Stab"_G(x) &|-> g x.
  $
]

== Discrete Subgroups & Lattices

Let $G$ be locally compact and $sigma$-compact, metric.
We assume that $d_G$ is a left-invariant metric on $G$ i.e.:
$
  d_G (g h_1, g h_2) = d_G (h_1, h_2).
$

#exercise[
  Let $G = "GL"_d (RR)$. Let $||dot||$ be a norm on $"Mat"_d (RR)$. Let
  $p: [0, 1] -> G$ be a continuous and pieceweise diffable. We define
  $
    L(p) = integral_0^1 ||p(t)^(-1) p'(t)|| dif t.
  $
  Then define
  $
    d(g_1, g_2) = inf {L(p) | p: [0, 1] -> G, p(0) = g_1, p(1) = g_2}.
  $
  Show that $d$ is a left-invariant metric on $G$.
]

We use the notation that $B_r^G$ is the ball of radius $r$ around $e$ in $G$.

#remark[
  Note that we have
  $
    (B_r^G)^(-1) = B_r^G,\
    B_r^G B_s^G subset B_(r+s)^G.
  $
  Indeed for the first one we note that $d(g, e) = d(e, g^(-1))$.
  For the second one we have
  $
    d(g_1 g_2, e) <= d(g_1 g_2, g_1) + d(g_1, e) = d(g_2, e) + d(g_1, e).
  $
]

Let $Gamma < G$ be a discrete subgroup. We define the quotient
$
  X = Gamma backslash G = {Gamma g | g in G}.
$
and the metric
$
  d_X(Gamma g_1, Gamma g_2)
  = inf {d_G (gamma_1 g_1, gamma_2 g_2) | gamma_1, gamma_2 in Gamma}
  = inf {d_G (gamma g_1, g_2) | gamma in Gamma}.
$

#exercise[
  Discrete subgroups are closed.
]

Since $Gamma$ is closed (its discrete) we have that the infimum only goes
to zero if $g_2 in Gamma g_1$.

#lemma[Injectivity Radius][
  For any compact subset $K subset X = Gamma backslash G$ there exists
  a *uniform injectivity raidus* $r > 0$ such that for any $x_0 in K$ the map
  $
    g in B_r^G |-> x_0 g in B_r^X (x_0)
  $
  is an isometry. Moreover for $K = {Gamma g_0}$ we can take
  $
    r = 1 / 4 inf_(gamma in Gamma backslash {e}) d_G (g_0^(-1) gamma g_0, e).
  $
]

#proof[
  We show the second claim first. Suppose $g_1, g_2 in B_r^G$ where
  $r$ is defined as in the lemma, $gamma in Gamma$ is such that
  $
    d(gamma g_0 g_1, g_0 g_2) < 2r.
  $
  We show that $gamma = e$. Then
  $
    d(g_0^(-1) gamma g_0 g_1, g_2) < 2r.
  $
  But we also have
  $
    d_G (g_2, e) < r
  $
  So we have by triangle inequality
  $
    d_G (g_0^(-1) gamma g_0 g_1, e)
    < 3 r.
  $
  Thus $g_0^(-1) gamma g_0 g_1 in B_(3r)^G$. And similarly
  $
    g_0^(-1) gamma^(-1) g_0 in B_(4r)^G.
  $
  By definition of $r$ (in the lemma) we must have $gamma = e$. Therefore
  $
    d_X (Gamma g_0 g_1, Gamma g_0 g_2)
    = inf_(gamma in Gamma) d_G (gamma g_0 g_1, g_0 g_2)
    = d_G (g_1, g_2) < 2r
  $
  Where the last equality comes from the above discussion.

  If $K$ is compact, then for any $x_0 in K$ we can find $r_0$ as above.
  Note that for $x in B_(r_0/2)^X (x_0)$ we can use $r_0 / 2$ as an
  injectivity radius. Using lebesgue numbers of this cover we
  can conclude the proof.
]

#definition[
  A measurable $F subset G$ is called

  - #[
      a fundamental domain if
      $
        G = union.big.sq_(gamma in Gamma) gamma F
      $
    ]

  - #[
      *injective* if $gamma_1 F, gamma_2 F$ are disjoint for all
      $gamma_1 != gamma_2 in Gamma$.
    ]
  - #[
      *surjective* if $G = union.big_(gamma in Gamma) gamma F$.
    ]
]

#remark[
  Note that the canonical projection
  $
    pi_X: G -> X = Gamma backslash G,
  $
  - we have $F$ is injective if and only if $pi_X|_F$ is injective.
  - we have $F$ is surjective if and only if $pi_X|_F$ is surjective.
  - $F$ is a fundamental domain if and only if $pi_X|_F$ is bijective.
]

#remark[
  Notice that this definition depends on the choice of $Gamma$, but
  we usually fix $Gamma$ implicitly.
]

#lemma[
  Let $B_"inj" subset B_"surj"$ bee injective respectively surjective
  sets in $G$. Then there exists a fundamental domain $F$ with
  $
    B_"inj" subset F subset B_"surj".
  $
]

#proof[
  Applying the previous lemma, we find a sequence of sets
  $
    B_n subset G
  $
  such that
  $
    pi_X|_(B_n)
  $
  is injective (i.e. $B_n$ is injective). We define
  $
    F_0 &= B_"inj",\
    F_1 &= B_"surj" inter B_1 backslash pi_X^(-1) (pi_X (F_0)), \
    ... \
    F_n &= B_"surj" inter B_n
    backslash pi_X^(-1)(pi_X (F_0 union ... union F_(n-1))).
  $
  Now we define $F = union.big_(n in NN) F_n$.
]

#definition[
  $Gamma$ is called a uniform lattice if $X = Gamma backslash G$ is compact.
]

#remark[
  Note that by our lemma about injectivity radius we can find in this case
  a finite union of balls of compact closure in $G$ whose images cover $X$.
  The union of all these balls are a surjective set with compact closure.
  In particular by the previous lemma we can find a fundamental domain
  with compact closure.
]

For the general definition of a lattice we need Haar measures.

Given $G$ metric, $sigma$-compact, locally compact.

#remark[
  These are the usual assumptions on topological groups for this course.
]

There exists a left (or right) Haar measrue $m_G$ on $G$ satisfying the usual
properties including uniqueness (see introduction to lie groups: @iozzi2025).

#definition[
  $G$ is called unimodular if $m_G$ is also right-invariant.
  I.e. left and right Haar measures coincide.
]

#lemma[
  If $B_1, B_2$ are injective sets with $pi_X (B_1) = pi_X (B_2)$ then
  $
    m_G (B_1) = m_G (B_2)
  $
]

#proof[
  We have
  $
    B_1 = union.big.sq_(gamma in Gamma) B_1 inter gamma B_2,\
    B_2 = union.big.sq_(gamma in Gamma) B_2 inter gamma^(-1) B_1.
  $
  by taking the measure on both sides the statment follows.
]

Given $X = Gamma backslash G$ and a fundamental domain $F$ we can define
$
  m_X (B) = m_G (F inter pi_X^(-1) (B)).
$
Because of hte previous lemma this does not depend on the choice of $F$.

#definition[
  $Gamma$ is called a lattice if $X = Gamma backslash G$ supports a
  right $G$-invariant finite measure.
]

#example[
  - $ZZ^d < RR^d$, is a uniform lattice.
  - $"SL"_d(ZZ) < "SL"_d(RR)$ is a lattice.
]

#proposition[
  TFAE:

  1. On $X = Gamma backslash G$ there exists a finite
    $G$-invariant measure.

  2. There exists a fundamental domain $F$ with finite right Haar measure $m_G^((r))$ which is left $Gamma$-invariant.

  3. There exists a fundamental domain $F$ with finite left Haar measure.
]

#remark[
  In particular if $G$ has a lattice then $G$ is unimodular.
]

Recall $mod: G times G -> RR^+$ is the modular character and is homomorphism, continous and satisfies

$
  m_G (B g) = mod(g) m_G (B).
$

for any left Haar measure $m_G$ and any measurable $B subset G$.


We will also use the poincarre recurrence theorem from ergodic theory. In a way it is the ergodic
pigeonhole principle.

#theorem[Poincarre][
  Let $X$ be locally compact $sigma$-compact metric space with a Borel probability measure $mu$. Let
  $T: X -> X$ be a measure-preserving continuous. Then for almost any $x in X$ there exists a sequence $n_k -> oo$ such that
  $
    T^(n_k) (x) -> x.
  $
]

#proof[
  1. #[
      ($3 => 2$):
      If $m_G(F) < oo$ then $mod(g) = m_G(F g) / m_G(F)$, but since $F g$ is another fundamental domain
      so we have $mod_G(g) = 1$. Thus $G$ is unimodular and $2$ follows.
    ]

  2. #[
      ($1 => 2$):
      Let $m_X$ be a right $G$-invariant probability measure on $X$. For $f >= 0$ on $G$ we define
      a new measure $mu$ such that
      $
        integral_G f dif mu = integral_X sum_(Gamma g = x) f(g) dif m_X (x).
      $
      We claim that
      - $mu$ is a right Haar measure on $G$
      - $mu(F) = integral 1 dif m_X = 1$ for any fundamental domain $F$
      - we have
        $
          mu(gamma_0 B) = integral_X sum_(gamma: gamma g in gamma_0 B) 1 dif m_X (Gamma g)\
          = integral_X sum_(gamma: gamma g in B) 1 dif m_X (Gamma g) = mu(B).
        $
      (we can use the injectivity radius to see that $mu$ is locally finite, whatever that means...)
      Hence we obtain the claim and $2$ follows.
    ]
  3. #[
      ($2 => 1$):
      We assume that $m_G^(r)(F) < oo$ for a fundamental domain $F$ and is left-$Gamma$-invariant.
      By lemma 3 (and its footnote) we have that any two injective with the same image have the same
      $m_G^r$-measure.

      We use this to define $m_X$:
      $
        m_X (B) = m_G^r (F inter pi_X^(-1)(B)).
      $ since the measure of $F$ is finite $m_X$ is a finite measure. Also $m_X$ is independent of the choice of $F$.
      We therefore have for $B subset X$ and $g in G$ that
      $
        m_X(B g) = m_G^r (F inter pi_X^(-1)(B g)) = m_G^r (F inter pi_X^(-1)(B) g) = m_G^r ((F g^(-1)) inter pi_X^(-1)(B))
        = m_X(B),
      $
      since $F g^(-1)$ is another fundamental domain. Thus $(1)$ follows.
    ]
  4. #[
      ($2 => 3$):
      We assume $m_X$ is a prob. measure $G$-invariant and $mod(G) = 1$. Let $B subset G$ be a compact nbh of $e in G$.
      Now we claim that $m_X (Gamma B) > 0$ (since open sets have non-zero measure). Let $g in G$ and define
      $
        T(x) = x g
      $
      The by poincarre recurrence there exists $Gamma b_0$ and a sequence $n_k arrow.tr oo$ with
      $
        Gamma b_0 g^(n_k) = Gamma b_k in Gamma B
      $
      By deifnition of $X$ there exists a sequence $gamma_k in Gamma$ with
      $
        b_0 g^(n_k) = gamma_k b_k
      $
      we apply $mod$ to get
      $
        mod(g)^(n_k) = mod(gamma_k b_k) / mod(b_0) = mod(b_k) / mod(b_0) in C
      $
      where $C subset (0, oo)$ is compact subset. But then $mod(g)^(n_k)$ cannot go to $oo$ or $0$ so $mod(g) = 1$.
      Thus $mod = 1$ and thus we have unimodularity and $3$ follows.
    ]
]

#proposition[Weil's Formula][
  Suppose $G$ is unimodular and $Gamma < G$ is discrete. Then there exists a locally finite (right) $G$-invariant
  measure $m_X$ on $X = Gamma backslash G$ satisfying
  $
    integral_G f dif m_G = integral_X sum_(gamma in Gamma) f(gamma g) dif m_X (Gamma g).
  $
  for $f in L^1(G, m_G)$. This is called "folding" or "unfolding".

  #remark[
    we say that $m_X$ is the Haar measure on $X$,... or uniform, volume, ... measure.
  ]
]

#remark[
  Number theorists prefer $Gamma backslash G$ whereas dynamicists prefer
  $G / Gamma$. However we dont care since these two ideas are isomorphic
  via:
  $
    Gamma g <--> g^(-1) Gamma.
  $
]

#proposition[Abstract divergence criterion][
  Let $Gamma < G$ be a lattice and $x_n = Gamma g_n in X = Gamma backslash G$.
  TFAE:

  1. $x_n -> oo$ as $n -> oo$, where $oo$ is the point of at infinity given by the one point compactification.
  2. The injectivity radius $r_(x_n)$ at $x_n$ converges to $0$ as $n -> oo$.
]

#proof[
  #[
    ($2 => 1$): We assume $r_(x_n) -> 0$. Suppose $x_n$ visits infinitely often
    a compact subset of $X$ this would contradict lemma 1 about inj. radius
    (i.e. inj. radius are uniform on compact sets).
  ]

  #[
    ($1 => 2$): We assume $x_n -> oo$. But $r_(x_n) >= epsilon$
    for all $n >= 1$ (take subsequence if necessary). By definition of
    injectivity radius we have $x_1 B_epsilon^G$ is an injective image of
    w.l.o.g. $overline(B_epsilon^G)$ is compact. By assumption there exists
    $N_1$ such that $x_n in.not x_1 B_epsilon^G$ for $n >= N_1$.
    By repeating the argument and taking subsequences we optain
    $
      x_1 B_epsilon^G in.rev.not x_2, x_3, ... \
      x_2 B_epsilon^G in.rev.not x_3, x_4, ... \
      ...
    $
    Let $g_n in G$ so that $x_n = Gamma g_n$. Then
    $
      g_n B_(epsilon / 2)^G
    $
    are all injective for $n >= 1$ and satisfy
    $
      union.big.sq_(n in NN) x_n B_(epsilon / 2)^G
    $
    is also a disjoint union. Hence
    $B = union.big.sq_(n in NN) g_n B_(epsilon / 2)^G$.
    But then $B$ has infinite volume and thus we get a contradiction.
  ]
]

#remark[
  Let $H < G$ be a closed subgroup. Then we can use $d_G$ to also define a metric
  on $H backslash G$.
]

$H < G$ also acts on $X = Gamma backslash G$. For any $x in X$ the orbit
$
  H dot x = x H isom H slash "Stab"_H(x) isom "Stab"_H(x) backslash H.
$
Recall that we defined $h dot x = x h^(-1)$ (so a left group
action by right multiplication).

#remark[Claim][
  $
    "Stab"_H(x) --> x H
  $
  is continuous.
]

#proof[of Claim][
  Suppose $Lambda = "Stab"_H(x) = H inter g^(-1) Gamma g$, with $x = Gamma g$.

  #remark[
    $"Stab"_G(Gamma g) = g^(-1) Gamma g.$
  ]

  Let $h_n in H$ satisfy $Lambda h_n -> Lambda h$ thus we can find
  $lambda_n in Lambda$ with $lambda_n h_n -> h$ in $H$ or in $G$.

  Recall that $lambda_n = g^(-1) gamma_n g$ for some $gamma_n in Gamma$.
  Thus $g lambda_n h_n = gamma_n g h_n -> g h$ in $G$. and thus
  $
    Gamma g h_n -> Gamma g h.
  $
  Thus the claim follows.
]

#definition[
  We say $x H$ has finite volume (or is a periodic point) if
  $
    "Stab"_H(x) < H
  $
  is a lattice (in $G$?).
]

#corollary[
  Suppose $x H$ has finite volume. Then $x H$ is closed and the map in the
  previous claim is proper. (i.e. extends to continuous map to one-point
  compactifications).
]

#proof[
  Suppose $lambda h_n -> oo$ in $Gamma backslash H$ as $n -> oo$.
  By the previous prop. that shows that the inj. rad at $Lambda h_n$
  goes to zero. This means that there exists a seq
  $lambda_n in Lambda$ so that
  $h_n^(-1) lambda_n h_n -> e$ in H as $n -> oo$. (see lemma 1).

  As abvoe we have $x = Gamma g$ and
  $Lambda = "Stab"_H (x) = g^(-1) Gamma g inter H$.
  This gives a $lambda_n = g^(-1) gamma_n g$ for some $gamma_n in Gamma$.
  and so
  $
    h_n^(-1) g^(-1) gamma_n g h_n -> e
  $
  as $n -> oo$.
  This shows that the injectivity radius at $Gamma g h_n$ goes to zero.
  Which we showed is equivalent to $Gamma g h_n -> oo$ in $X$ (by the lemma).

  Suppose now $x h_n -> z in X$ as $n -> oo$. In particular $x h_n$ does not
  go to infinity. Thus by the previous part we have that
  $Lambda h_n in Lambda backslash H$ does not go to infinity in
  $Lambda backslash H$. Hence a subsequence convergece say to
  $
    Lambda h
  $
  applying continuity we optain $z = x h in x H$.
]

#remark[
  If a sequence does not go to infinity it has convergent subsequences
  (in the sense of one-point compactification).
]

#proposition[
  If $x H$ is a closed orbit then the map above from
  $
    "Stab"_H(x) backslash H -> x H subset X = Gamma backslash G
  $
  is a homeomorphism. In particular, the Haar measure on
  $"Stab"_H(x) backslash H$ gives rise to a locally finite
  measure on $X$ (with support in $x H$).
]


#bibliography("bib.bib", full: true)
