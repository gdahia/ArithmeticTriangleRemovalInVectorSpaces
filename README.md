# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

Lean 4 formalization of the main results of Jacob Fox and László Miklós Lovász,
[*A tight bound for Green's arithmetic triangle removal lemma in vector
spaces*](https://arxiv.org/abs/1606.01230): Theorems 1, 2 and 3, including both parts of
Theorem 2, the construction of Section 3, the bound $\delta \le \varepsilon^{C_p - o(1)}$ that
these give, and the values of $c_2$ and $c_3$.

## Results

Let $p$ be a prime. A triangle of $X \times Y \times Z$ is a triple $(x, y, z)$ with
$x + y + z = 0$; in Lean, `triangles X Y Z`. A family of triples $(x_i, y_i, z_i)_{i \in I}$ is
multicolored sum-free if $x_i + y_j + z_k = 0$ holds exactly when $i = j = k$; in Lean,
`IsMulticoloredSumFree x y z`. The exponents `c p` and `C p` are defined by

$$p^{1 - c_p} = \inf_{0 < x < 1} x^{-(p-1)/3} \left(1 + x + \cdots + x^{p-1}\right), \qquad
C_p = 1 + \frac{1}{c_p}.$$

Write $N = p^n$.

**Theorem 1**
(`ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_triangles_eq_empty`,
Theorem 1 of the paper, first part). Let $\varepsilon \ge 0$ and $X, Y, Z \subseteq \mathbb{F}_p^n$.
If $X \times Y \times Z$ contains fewer than $(\varepsilon / 3)^{C_p} N^2$ triangles, then there are
$X' \subseteq X$, $Y' \subseteq Y$ and $Z' \subseteq Z$ with

$$|X \setminus X'| + |Y \setminus Y'| + |Z \setminus Z'| \le \varepsilon N$$

such that $X' \times Y' \times Z'$ contains no triangle.

**Theorem 2** (`ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_rpow_mul`,
Theorem 2 of the paper, first part, due to Kleinberg, Sawin and Speyer). A multicolored sum-free
family of $m$ triples in $\mathbb{F}_p^n$ has $m \le p^{(1 - c_p) n}$.

**Theorem 3** (`ArithmeticTriangleRemovalInVectorSpaces.div_pow_rpow_C_mul_sq_le_card_triangles`,
Theorem 3 of the paper). If $X \times Y \times Z$ contains $m$ vertex-disjoint triangles in
$\mathbb{F}_p^n$, then it contains at least $(m / N)^{C_p} N^2$ triangles.

**Theorems 4, 5 and 6**
(`ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_of_card_triangles_lt`,
`ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_card_rpow` and
`ArithmeticTriangleRemovalInVectorSpaces.div_rpow_C_mul_sq_le_card_triangles`). Theorems 1, 2
and 3 hold in every finite vector space $V$ over $\mathbb{F}_p$, with $N = |V|$.

**Theorem 7**
(`ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_prod_pi` and
`ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.triangles_prod_pi_nonempty`,
Section 3 of the paper). Let $(x_i, y_i, z_i)$ be a multicolored sum-free family of $m$ triples in
$\mathbb{F}_p^n$ with vertex sets $X$, $Y$ and $Z$, and let $W = \mathbb{F}_p^l$. Then
$(X \times W) \times (Y \times W) \times (Z \times W)$ contains exactly $m p^{2l}$ triangles, and
removing fewer than $m p^l$ elements from $X \times W$, $Y \times W$ and $Z \times W$ leaves a
triangle.

**Theorem 8**
(`ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset`).
Suppose that every $X, Y, Z \subseteq \mathbb{F}_p^n$ with fewer than $\delta N^2$ triangles can
be made triangle-free by removing at most $\varepsilon N$ elements. Then every multicolored
sum-free family of $m > \varepsilon N$ triples in $\mathbb{F}_p^n$ has $\delta N^2 \le m$.

**Theorem 9** (`ArithmeticTriangleRemovalInVectorSpaces.exists_pos_forall_le_rpow_C_sub`,
Theorem 1 of the paper, second part, as derived in Section 3). For every $\eta > 0$ there is
$\varepsilon_0 > 0$ such that for $0 < \varepsilon < \varepsilon_0$, any $\delta$ that works with
$\varepsilon$ in Theorem 1 for every $n$ satisfies $\delta \le \varepsilon^{C_p - \eta}$. The
proof combines Theorems 8 and 11.

**Theorem 10** (`ArithmeticTriangleRemovalInVectorSpaces.c_two` and
`ArithmeticTriangleRemovalInVectorSpaces.c_three`).

$$c_2 = \frac{5}{3} - \log_2 3, \qquad c_3 = 1 - \frac{\log b}{\log 3}, \quad
b = a^{-2/3} + a^{1/3} + a^{4/3}, \quad a = \frac{\sqrt{33} - 1}{8}.$$

**Theorem 11**
(`ArithmeticTriangleRemovalInVectorSpaces.exists_forall_ge_exists_isMulticoloredSumFree`,
Theorem 2 of the paper, second part, due to Kleinberg, Sawin and Speyer with Pebody). Let
$p \ge 2$, not necessarily prime, and $\eta > 0$. For every large $n$ there is a multicolored
sum-free family in $(\mathbb{Z} / p \mathbb{Z})^n$ with at least $p^{(1 - c_p - \eta) n}$ triples.

## Proof

The proof follows the paper, with three changes.

* Lemma 5 of the paper bounds the number of triangles when every vertex lies in at most
  $\rho N$ triangles. The paper intersects $X$, $Y$ and $Z$ with a uniformly random subspace; the
  Lean proof uses the kernel of a uniformly random linear map, and the lemma holds for every
  $\rho$.
* Lemma 6 and Theorem 4 of the paper remove vertices of large degree one at a time and give
  Theorem 3 with the exponent $C_p + o(1)$. The Lean proof instead chooses subsets minimizing a
  potential, which gives Theorem 3 up to a constant factor. The product argument of the paper then
  removes the constant factor.
* The values of $c_2$ and $c_3$ follow from the weighted arithmetic-geometric mean inequality.

Theorem 2 is proved by the slice rank method, with Tao's lemma on the slice rank of a diagonal
tensor, a Chernoff bound for the number of monomials of low degree, and a product argument that
removes the constant factor $3$.

Theorem 11 follows Kleinberg, Sawin and Speyer, *The growth rate of tri-colored sum-free sets*,
with Pebody, *Proof of a conjecture of Kleinberg, Sawin and Speyer*.

* Pebody's theorem says that three decreasing mass functions on $[0, N]$ with equal masses whose
  means sum to $N$ are the marginals of a nonnegative function on the triples with sum $N$. It is
  proved by induction on $N$: decreasing mass functions are combinations of uniform distributions,
  balanced weights decompose into simple triples (Lemma 2.1 of Pebody), and the simple triples
  are handled by peeling off a layer (Lemma 3.1 and Corollary 3.2) or by a case analysis
  (Section 5).
* With $N = p - 1$ and the geometric distribution $\rho^k$ of mean $N / 3$, rounding down a
  multiple of the coupling gives a base point in $\{0, \dots, p - 1\}^n$. The empirical
  distribution of each of its three coordinates is within a bounded distance of a multiple of
  $\rho^k$, so their type classes have at least
  $(\rho^{-N/3} \sum_k \rho^k)^n e^{-O(\log n)} \ge p^{(1 - c_p) n} e^{-O(\log n)}$ elements
  (Lemma 3.1 of Kleinberg, Sawin and Speyer).
* The triples of the three type classes summing to the all $p - 1$ vector are hashed into
  $\mathbb{Z} / P \mathbb{Z}$, for a prime $P$ from Bertrand's postulate, and the triples whose
  hashes lie in a set without three-term progressions from Behrend's construction and share no
  vector with another such triple form a multicolored sum-free family (Section 4 of Kleinberg,
  Sawin and Speyer). Adding $1$ to the third vector of each triple gives a family in
  $(\mathbb{Z} / p \mathbb{Z})^n$, and padding by zero coordinates gives every large dimension.

## Files

| Files in `ArithmeticTriangleRemovalInVectorSpaces/` | Contents |
| --- | --- |
| `Triangle/Basic.lean` | The triangles of $X \times Y \times Z$ |
| `LinearMap/Card.lean` | The number of linear maps vanishing at independent vectors |
| `SliceRank/Diagonal.lean` | Tao's lemma on the slice rank of a diagonal tensor |
| `MulticoloredSumFree/Basic.lean` | Multicolored sum-free families |
| `MulticoloredSumFree/Monomials.lean` | The Chernoff bound for the monomials of low degree |
| `MulticoloredSumFree/SliceRank.lean` | The slice rank bound for multicolored sum-free families |
| `MulticoloredSumFree/Exponent.lean` | $c_p$ and $C_p$ |
| `MulticoloredSumFree/TensorPower.lean` | Theorem 5 |
| `MulticoloredSumFree/Product.lean` | The construction of Section 3 in a finite abelian group |
| `MulticoloredSumFree/SmallPrimes.lean` | Theorem 10 |
| `DisjointTriangles/Sampling.lean` | Lemma 5 of the paper |
| `DisjointTriangles/Pruning.lean` | Theorem 3 up to a constant factor, in general position |
| `DisjointTriangles/Embedding.lean` | The embedding into general position |
| `DisjointTriangles/TensorPower.lean` | Theorem 6 |
| `DisjointTriangles/MaximalFamily.lean` | Theorem 4 |
| `Tightness/Exponent.lean` | The real arithmetic of Theorem 9 |
| `Coupling/Basic.lean` | Compatible mass functions |
| `Coupling/Peeling.lean` | Lemma 3.1 and Corollary 3.2 of Pebody |
| `Coupling/Uniform.lean` | Uniform distributions and the case analysis of Pebody's Section 5 |
| `Coupling/Decomposition.lean` | Lemma 2.1 of Pebody |
| `Coupling/Pebody.lean` | Pebody's theorem and the geometric distribution |
| `Construction/TypeClass.lean` | The size of a type class |
| `Construction/Behrend.lean` | Sets without three-term progressions in $\mathbb{Z} / P \mathbb{Z}$ |
| `Construction/Hash.lean` | The hashing argument of Kleinberg, Sawin and Speyer |
| `Construction/Family.lean` | The multicolored sum-free family of a base point |
| `Construction/LowerBound.lean` | Theorem 11 |
| `ZMod.lean` | Theorems 1, 2, 3, 7, 8 and 9 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the scope,
and the use of AI coding agents.

## Verification

`Challenge.lean` imports only the Mathlib module `Mathlib.Analysis.SpecialFunctions.Log.Base`. It
repeats the library definitions of `triangles`, `IsMulticoloredSumFree`, `c` and `C`, and states
Theorems 1 to 11 as `exists_subset_card_sdiff_add_le_triangles_eq_empty'`,
`IsMulticoloredSumFree.card_le_rpow_mul'`, `div_pow_rpow_C_mul_sq_le_card_triangles'`,
`exists_subset_card_sdiff_add_le_of_card_triangles_lt'`,
`IsMulticoloredSumFree.card_le_card_rpow'`, `div_rpow_C_mul_sq_le_card_triangles'`,
`IsMulticoloredSumFree.card_triangles_prod_pi'`,
`IsMulticoloredSumFree.triangles_prod_pi_nonempty'`,
`IsMulticoloredSumFree.mul_sq_le_card_of_forall_exists_subset'`,
`exists_pos_forall_le_rpow_C_sub'`, `c_two'`, `c_three'` and
`exists_forall_ge_exists_isMulticoloredSumFree'` with `sorry`. `comparator.json`
names these theorems, `ArithmeticTriangleRemovalInVectorSpacesPalomar.Challenge` and
`ArithmeticTriangleRemovalInVectorSpacesPalomar.Solution` as the modules to compare, and `propext`,
`Classical.choice` and `Quot.sound` as the permitted axioms. The two modules sit in
`ArithmeticTriangleRemovalInVectorSpacesPalomar/` rather than at the root, so that they do not
clash with the `Challenge` and `Solution` modules of other Palomar submissions.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
statements, with the expected `sorry` warnings.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
