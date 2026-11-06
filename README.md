# A tight bound for Green's arithmetic triangle removal lemma in vector spaces

Lean 4 formalisation of the main results of Jacob Fox and László Miklós Lovász,
[*A tight bound for Green's arithmetic triangle removal lemma in vector
spaces*](https://arxiv.org/abs/1606.01230): the arithmetic triangle removal lemma in
$\mathbb{F}_p^n$ with a polynomial bound (Theorem 1), the Kleinberg–Sawin–Speyer bound on
multicolored sum-free families (Theorem 2), the count of triangles spanned by vertex-disjoint
triangles (Theorem 3), and the tightness of the exponent in Theorem 1 (Theorem 4).

## Results

**Theorem 1** (`exists_subset_card_sdiff_add_le_forall_add_ne_zero`, Theorem 1 of the paper). Let
$p$ be a prime, $n \ge 0$, $N = p^n$, $\varepsilon \ge 0$ and $X, Y, Z \subseteq \mathbb{F}_p^n$.
If $X \times Y \times Z$ contains fewer than $(\varepsilon / 3)^{C_p} N^2$ triangles, then there
are $X' \subseteq X$, $Y' \subseteq Y$ and $Z' \subseteq Z$ with

$$|X \setminus X'| + |Y \setminus Y'| + |Z \setminus Z'| \le \varepsilon N$$

such that $X' \times Y' \times Z'$ contains no triangle, where a triangle is a triple $(x, y, z)$
with $x + y + z = 0$, $C_p = 1 + 1 / c_p$, and $c_p$ is defined by

$$p^{1 - c_p} = \inf_{0 < x < 1} x^{-(p-1)/3} \left(1 + x + \cdots + x^{p-1}\right).$$

**Theorem 2** (`card_le_rpow_one_sub_c_mul`, Theorem 2 of the paper, due to Kleinberg, Sawin and
Speyer). Let $p$ be a prime and let $(x_i, y_i, z_i)_{i \in I}$ be a finite family of triples in
$\mathbb{F}_p^n$. If $x_i + y_j + z_k = 0$ holds exactly when $i = j = k$, then

$$|I| \le p^{(1 - c_p) n},$$

where $c_p$ is as in Theorem 1.

**Theorem 3** (`div_pow_rpow_C_mul_sq_le_card_triangles`, Theorem 3 of the paper). Let $p$ be a
prime, $N = p^n$ and $X, Y, Z \subseteq \mathbb{F}_p^n$. If $X \times Y \times Z$ contains $m$
vertex-disjoint triangles, then it contains at least

$$\left(\frac{m}{N}\right)^{C_p} N^2$$

triangles, where $C_p$ is as in Theorem 1.

**Theorem 4** (`le_rpow_C_sub_of_forall_exists_subset`, the second part of Theorem 1 of the
paper). Let $p$ be a prime, $\eta > 0$, and put

$$\eta' = \frac{c_p \min(1 - c_p, c_p \eta / 2)}{2}, \qquad
n_0 = \left\lceil \left(\frac{2^{p+3} p^{10}}{\eta'}\right)^2 \right\rceil + p^4 + 1, \qquad
\varepsilon_0 = p^{-(n_0 + 1)}.$$

The following holds for every $0 < \varepsilon < \varepsilon_0$ and every $\delta$. If for every
$n$, every $X, Y, Z \subseteq \mathbb{F}_p^n$ with fewer than $\delta N^2$ triangles, where
$N = p^n$, has subsets $X' \subseteq X$, $Y' \subseteq Y$ and $Z' \subseteq Z$ with
$|X \setminus X'| + |Y \setminus Y'| + |Z \setminus Z'| \le \varepsilon N$ such that
$X' \times Y' \times Z'$ contains no triangle, then

$$\delta \le \varepsilon^{C_p - \eta},$$

where triangles and $C_p$ are as in Theorem 1.

## Files

| Directory in `ArithmeticTriangleRemovalInVectorSpaces/` | Contents |
| --- | --- |
| `Triangle/` | The triangles of $X \times Y \times Z$ |
| `LinearMap/` | The number of linear maps vanishing at independent vectors |
| `SliceRank/` | The slice rank of a diagonal tensor |
| `MulticoloredSumFree/` | Multicolored sum-free families, the slice rank bound, $c_p$ and $C_p$ |
| `DisjointTriangles/` | Triangles spanned by vertex-disjoint triangles, and the removal lemma |
| `Tightness/` | Real inequalities for the exponent $C_p$ |
| `Coupling/` | Couplings of decreasing mass functions |
| `Construction/` | Large multicolored sum-free families |
| `ZMod.lean` | Theorems 1 to 4 in $\mathbb{F}_p^n$ |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the scope,
and the use of AI coding agents.

## Verification

`Challenge.lean` imports only the Mathlib module `Mathlib.Analysis.SpecialFunctions.Log.Base`. It
defines `c`, `C`, `n₀` and `ε₀` as in the library and states Theorems 1 to 4 as
`exists_subset_card_sdiff_add_le_forall_add_ne_zero'`, `card_le_rpow_one_sub_c_mul'`,
`div_pow_rpow_C_mul_sq_le_card_triangles'` and `le_rpow_C_sub_of_forall_exists_subset'` with
`sorry`.
`comparator.json` names these theorems,
`ArithmeticTriangleRemovalInVectorSpacesPalomar.Challenge` and
`ArithmeticTriangleRemovalInVectorSpacesPalomar.Solution` as the modules to compare, no
definitions, and `propext`, `Classical.choice` and `Quot.sound` as the permitted axioms. The two
modules sit in `ArithmeticTriangleRemovalInVectorSpacesPalomar/` rather than at the root, so that
they do not clash with the `Challenge` and `Solution` modules of other Palomar submissions.

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
