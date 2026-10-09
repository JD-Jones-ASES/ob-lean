# The proofs, with the Lean names

`h : Fin n → ℤ` is a Barker sequence (`IsBarker h`): every `h j` is `1` or `-1` (`IsSign`) and
`|aperiodic h k| ≤ 1` for `0 < k < n`, where `aperiodic h k = C(k) = ∑_{j < n−k} h j · h (j+k)`. The
definitions are in `OB/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module named below, restated in `Solution.lean`.

**Conventions.** `a = seq h : ℕ → ℤ` extends `h` by zero off `[0, n)` (`seq`, `seq_eq`, `seq_of_le`);
`aperiodic h k = ∑_{j < n−k} a j · a (j+k)` (`aperiodic_eq_sum`); `a i ∈ {±1}` for `i < n` (`seq_sign`,
`seq_mul_self`). `m = (n − 1)/2`. For `s ≥ 1`, `d s = a (s−1) · a s`; `s` is a *sign change* when `d s = −1`.
`T0 a w = ∑_{k ≤ w} (−1)^k a k · a (w−k)` (`T0`, `OB/Identity.lean`). For a finite family of signs `x_i`,
`∏ x_i = 1 − ((card − ∑ x_i) mod 4)`, and `card − ∑ x_i` is even (`prod_signs`): the product is `(−1)` to the
number of `−1`s. All of this is in `OB/Bridge.lean`.

## Part A. Barker ⇒ three identities (S), (F), (D)

**Shifts (`OB/Parity.lean`).** Every term of `C(k)` is a sign, so `C(k) ≡ n − k (mod 2)` (`aperiodic_parity`);
for odd `n` and odd `k` it is even with `|C(k)| ≤ 1`, so `C(k) = 0` (`odd_shift_zero`). Splitting the cyclic
sum at `n − u`, `C(u) + C(n−u) = ∑_{j<n} a j · a ((j+u) mod n)`. For signs, `xy ≡ x − y + 1 (mod 4)`, and
`∑_j (a j − a ((j+u) mod n)) = 0` since the shift permutes `[0, n)`; so `C(u) + C(n−u) ≡ n (mod 4)`
(`aperiodic_add_aperiodic_sub_mod_four`). For odd `n` and even `u`, `n − u` is odd, so `C(n−u) = 0`,
`C(u) ≡ n (mod 4)` with `|C(u)| ≤ 1` odd, and `C(u) = (−1)^m` (`even_shift_eq`). Together these are
**`aperiodic_eq`** (`aperiodic_eq_internal`).

**(S) Skew-symmetry (`OB/Skew.lean`).** Put `P(u) = ∏_{j < n−u} a j · a (j+u)`; by `prod_signs`,
`P(u) = 1 − (((n−u) − C(u)) mod 4)` (`prod_shift_eq`). Writing `P(u)` and `P(u+1)` as products of a prefix and a
shifted block, the common factors are squares of signs and cancel, leaving `P(u) · P(u+1) = a u · a (n−1−u)`.
One of `u`, `u+1` is odd (`C = 0`) and the other even (`C = (−1)^m`); reading the residues of `n` and `u` mod 4
gives `a k · a (n−1−k) = (−1)^{m+k}` (`skew_seq`), which is **`skew`** (`skew_internal`, with `Fin.rev`).
In sign-change form: `d s · d (n−s) = [a (s−1) a (n−s)] · [a s a (n−1−s)] = (−1)^{m+s−1} (−1)^{m+s} = −1`
for `1 ≤ s ≤ n−1` (`skew_pair`): **`s` is a sign change iff `n − s` is not.**

**(F) The folded identity (`OB/Fold.lean`).** For even `w ≤ n − 3`, `n − 1 − w` is an even shift, so
`C(n−1−w) = (−1)^m`. In `C(n−1−w) = ∑_{j ≤ w} a j · a (j+n−1−w)`, (S) at `k = w − j` rewrites
`a (j+n−1−w) = (−1)^{m+w−j} a (w−j)`, and `(−1)^{w−j} = (−1)^w (−1)^j` (`neg_one_pow_sub`); with `w` even,
`C(n−1−w) = (−1)^m T0 a w`, so `T0 a w = 1` (`fold_seq`). This is **`fold`** (`fold_internal`).

**(D) Doubling (`OB/Fold.lean`).** Split `T0 a (2j)` at its middle term `a j² = 1` and reflect the upper half
(`Finset.sum_range_reflect`): `T0 a (2j) = 2 ∑_{k<j} t_k + (−1)^j` with `t_k = (−1)^k a k · a (2j−k)`. So
`∑_{k<j} t_k = (1 − (−1)^j)/2`, and `prod_signs` gives `∏_{k<j} t_k = (−1)^{j(j−1)/2} = ∏_{k<j} (−1)^k`; hence
`∏_{k<j} a k · a (2j−k) = 1`, i.e. `∏_{i ≤ 2j} a i = a j` for `2j ≤ n − 3` (`prod_prefix`). Dividing the prefix
products at `2u` and `2u − 2` gives `a (2u−1) · a (2u) = a (u−1) · a u` for `1 ≤ u`, `2u + 3 ≤ n`
(`doubling_seq`): **`d u = d (2u)`**. This is **`doubling`** (`doubling_internal`).

## Part B. The sign changes (`OB/Runs.lean`, `OB/KeyBound.lean`)

From here on only (S) in the form `skew_pair`, (D) in the form `doubling_seq`, and (F) are used. Let `n ≥ 7` and
`a 0 = a 1`; `p` is the least sign change (the paper's `s₁`, the length of the first run) and `q` the least sign
change not divisible by `p` (the paper's `s_e`). The run decomposition and the index `e` are never needed.

**`p`.** `2 ≤ p` (`two_le_p`, from `a 0 = a 1`). Positions `1, …, p−1` are not changes, so by `skew_pair`
positions `n−1, …, n−p+1` are, and `n − p + 1 ≥ p`: `2p ≤ n + 1` (`two_mul_p_le`). If `p` were even, `doubling_seq`
at `u = p/2` would make `p/2 < p` a change: `p` is odd (`p_odd`), so `p ≥ 3`.

**`q` exists and `p < q`.** `d 1 = d 2 = 1`, so `n − 1` and `n − 2` are changes (`skew_pair`), and `p ≥ 3` divides
at most one of two consecutive numbers (`exists_q`). As `p ∣ p`, `q ≠ p`, and `q ≥ p` since `q` is a change
(`p_lt_q`).

**Lemma 3: `2q − 3 ≤ n` and `q` odd.** If `2q > n + 3`, the windows `[1, q)` and `(n − q, n)` share three
consecutive positions `s, s+1, s+2`. In the first window a position is a change iff `p` divides it (minimality of
`q`); in the second, by `skew_pair`, it is a change iff `n − s'` is not. Two of `n − s, n − s − 1, n − s − 2` would
then be multiples of `p ≥ 3` differing by 1 or 2: impossible (`two_mul_q_le`). If `q` were even, `doubling_seq` at
`u = q/2` would make `q/2 < q` a change, so `p ∣ q/2 ∣ q`: `q` is odd (`q_odd`).

**Lemma 4: `n ≤ p + q + 1`.** The step identity (`T0_step`, `OB/Identity.lean`): for every `a : ℕ → ℤ` and even
`w`, with `Δ t = a (t+1) − a t`,
`T0 a (w+2) − T0 a w = 2 a 0 · Δ (w+1) − ∑_{t ≤ w} (−1)^t Δ t · Δ (w−t)`,
the coefficient of `x^{w+2}` in `(1 − x²) a(x) a(−x) = [(1 − x) a(x)] [(1 + x) a(−x)]`; and `T0 a (w+1) = 0`
(`T0_odd`). If `p + q + 3 ≤ n`, (F) gives `T0 a (p+q−2) = T0 a (p+q) = 1`, so the left side is `0`. `Δ t ≠ 0`
only when `t + 1` is a change; a pair of changes `(s, s')` with `s + s' = p + q` has both `≥ p`, hence both
`≤ q`, and if both were `< q` then `p ∣ p + q`, against `p ∤ q`. So the pairs are `(p, q)` and `(q, p)`, the sum is
`±8`, while `|2 a 0 · Δ| ≤ 4`: contradiction (`key_bound`, which uses only the signs of `a` on `[0, p+q]`). Hence
`n ≤ p + q + 1` (`n_le_p_add_q_add_one`). This one identity replaces the paper's run-by-run telescoping of
`C(n−v+1) − C(n−v−1)`.

Collected: `run_bounds_seq`, and **`run_bounds`** (`run_bounds_internal`) on `Fin n`.

## The endgame and the alternation (`OB/Endgame.lean`)

From `2q − 3 ≤ n ≤ p + q + 1` with `p < q` both odd: `q ∈ {p + 2, p + 4}`.

- `q = p + 2`, so `n ∈ {2p + 1, 2p + 3}`. `doubling_seq` at `u = p − 1` says `2p − 2` is not a change (`p − 1` is
  not), so `n − 2p + 2` is (`skew_pair`). If `n = 2p + 1` that is `3 < q`, so `p ∣ 3`: `p = 3`, `n = 7`. If
  `n = 2p + 3` it is `5`, so `p ∣ 5` or `5 = q`: `p = 5` gives `n = 13`; `p = 3` gives `n = 9`, where
  `doubling_seq` at `u = 3` makes `6` a change (`3 = p` is one) while `skew_pair` at `s = 3` says `6 = 9 − 3` is not.
- `q = p + 4`, so `n = 2p + 5`. Since `(p+2) + (p+3) = n`, exactly one of them is a change (`skew_pair`); both are
  `< q`, so `p` divides it; `p ∤ p + 2`, so `p ∣ p + 3`: `p = 3`, `n = 11`.

So `n ∈ {7, 11, 13}` (`endgame`). The alternation `alt h j = (−1)^j h j` multiplies `C(k)` by `(−1)^k`
(`aperiodic_alt`), so it preserves `IsBarker` (`isBarker_alt`) and turns `h 0 ≠ h 1` into `h 0 = h 1`. For
`n ≥ 7`, after this normalization, `p` and `q` are taken by `Nat.find` (the first change exists: `skew_pair` at
`s = 1` makes `n − 1` one; `q` by `exists_q`), and `endgame` applies; `n ≤ 5` odd is already in the list. This is
**`odd_length_mem`** (`odd_length_mem_internal`). The same argument as at `n = 9` (`doubling_seq` at `u = k`
against `skew_pair` at `s = k`) excludes every `n = 3k` with `k ≥ 3` odd; that remark is not needed and is not
formalized.

**Witnesses (`OB/Witnesses.lean`).** Eight explicit sequences `a1, a2, a3, a4, a5, a7, a11, a13` are Barker
(`aN_isBarker`), each by `decide` over its shifts; the control `forged13` (the last sign of `a13` flipped,
`C(1) = 2`) is proved not Barker (`forged13_not_isBarker`). With `odd_length_mem`, this is **`odd_exists_iff`**
(`odd_exists_iff_internal`, `OB/Compose.lean`).

## The even reduction (`OB/Hadamard.lean`; Turyn–Storer, footnote 2)

For even `n` every even shift has `C(k) ≡ n − k ≡ 0 (mod 2)`, hence `C(k) = 0` (`even_shift_zero_of_even`). At
`u = 2` the mod-four congruence gives `0 = C(2) + C(n−2) ≡ n (mod 4)`: **`four_dvd_of_even`**
(`four_dvd_of_even_internal`). The periodic autocorrelation `periodic h a = ∑_j h j · h (j − a)` (`periodic`) is
`n` at `a = 0` (`periodic_zero`) and `C(a) + C(n − a)` otherwise (`periodic_eq_aperiodic_add`); it lies in
`[−2, 2]` and is `≡ n ≡ 0 (mod 4)`, so it vanishes off the peak (`periodic_offpeak_zero`). The circulant matrix
`circ h i j = h (j − i)` is circulant (`circ_isCirculant`), a sign matrix, and has
`(H Hᵀ) i j = periodic h (j − i)`, so `H Hᵀ = n I` (`circ_isSignHadamard`): **`existsRealCirculantHadamard_of_even`**
(`existsRealCirculantHadamard_of_even_internal`). The route follows `lean/OAI/LinearAlgebra/Barker/` of openai/math
in outline; the definition `periodic` is adapted from its `Model.lean` (NOTICE).

## The compositions (`OB/Compose.lean`, `OB/Hadamard.lean`)

**`exists_iff_of_even`** (`exists_iff_of_even_internal`): split `n` by parity; even `n` is `2` or `4` by the
hypothesis `heven`, odd `n` is in the list by `odd_length_mem`; conversely the eight witnesses.
**`length_le_thirteen_of_even`** (`length_le_thirteen_of_even_internal`): `n = 0` is trivial, otherwise read the
list. From the circulant hypothesis `hcirc`: an even Barker length `n > 0` is `2`, or `n > 2` and the even
reduction gives a circulant Hadamard matrix of order `n`, so `n ∈ {1, 4}` and, being even, `n = 4`
(`even_length_eq_two_or_four_of_circulantHadamard`); feeding this to the previous two gives
**`exists_iff_of_circulantHadamard`** and **`length_le_thirteen_of_circulantHadamard`** (their `_internal` forms).

<!-- DESK: if `unique` (OB/Unique.lean, `canon`, `unique_internal`) closes and enters the Challenge, add a section:
for odd n, (S) determines h from its first m + 1 values, and a kernel check over those values at each of the six
lengths shows h = ±canon n or ±alt (canon n). -->

## Relation to the sources

Turyn and Storer's Theorem 2 states `n ≤ 13` for odd `n`; the list `{1, 3, 5, 7, 11, 13}` is in their
introduction. Theorem 1(iv) of Turyn–Storer is false as stated (Willms 2014); per Schmidt–Willms the induction
survives with a corrected range; the theorem itself was never in doubt. Nothing of Theorem 1 is used here.
Schmidt–Willms's Lemma 2 is `aperiodic_eq`, (S) and (D) (`skew`, `doubling`); their Lemmas 3 and 4 are
`run_bounds`; their final three cases are `endgame`. The recast differs from the paper in three places: (F) is
stated once and (D) and Lemma 4 are derived from it; `p` and `q` are defined directly on the sign changes, without
the run decomposition; and Lemma 4 is one generating-function identity with a two-point pair set instead of a
telescoping case analysis.
