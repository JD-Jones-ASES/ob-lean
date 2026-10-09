# Barker sequences of odd length have length 1, 3, 5, 7, 11 or 13

A Barker sequence of length `n` is a `±1` sequence `h₀, …, h_{n−1}` whose aperiodic autocorrelations
`C(k) = ∑_{j<n−k} h_j h_{j+k}`, `0 < k < n`, all satisfy `|C(k)| ≤ 1`. Turyn and Storer (*On binary sequences*,
Proc. Amer. Math. Soc. 12 (1961) 394–399) proved that a Barker sequence of odd length has length 1, 3, 5, 7, 11
or 13. Theorem 1(iv) of Turyn–Storer is false as stated (Willms 2014, arXiv:1404.4833); per Schmidt–Willms the
induction survives with a corrected range; the theorem itself was never in doubt. The proof formalized here is
Schmidt and Willms's (*Barker sequences of odd length*, Des. Codes Cryptogr. 80 (2016) 409–414,
arXiv:1501.06035), recast so that no case enumeration is needed.

With the seven definitions restated character for character from two challenge files of openai/math at commit
`adc7f124` (Apache-2.0, see [NOTICE](NOTICE); namespace `OddBarker`), [Challenge.lean](Challenge.lean) states
thirteen theorems and [Solution.lean](Solution.lean) proves them, kernel-only; the table in
[VERIFICATION.md](VERIFICATION.md) names each one. Unconditionally:

- for odd `n`, a Barker sequence of length `n` exists iff `n ∈ {1, 3, 5, 7, 11, 13}` (`odd_length_mem`,
  `odd_exists_iff`);
- for odd `n` and `m = (n − 1)/2`: `C(k) = 0` at odd shifts and `(−1)^m` at even ones (`aperiodic_eq`);
  `h_k h_{n−1−k} = (−1)^{m+k}` (`skew`); `∑_{k≤w} (−1)^k h_k h_{w−k} = 1` for even `w ≤ n − 3` (`fold`);
  `h_{u−1} h_u = h_{2u−1} h_{2u}` for `1 ≤ u ≤ (n − 3)/2` (`doubling`); and Schmidt–Willms's Lemmas 3 and 4: for
  `n ≥ 7` and `h₀ = h₁`, with `p` the first sign change and `q` the first one not divisible by `p`, both are odd
  and `2q − 3 ≤ n ≤ p + q + 1` (`run_bounds`);
- Turyn–Storer's even reduction: a Barker sequence of even length `n > 2` has `4 ∣ n` and yields a real circulant
  Hadamard matrix of order `n` (`four_dvd_of_even`, `existsRealCirculantHadamard_of_even`).

Given the even-length classification as an explicit hypothesis (every Barker sequence of positive even length has
length 2 or 4: `even_length_eq_two_or_four` of openai/math, family 179), Barker sequences of positive length exist
exactly at `n ∈ {1, 2, 3, 4, 5, 7, 11, 13}`, and every Barker sequence has length at most 13
(`exists_iff_of_even`, `length_le_thirteen_of_even`). The same follows, through the even reduction, from the
hypothesis that real circulant Hadamard matrices of positive order exist only at orders 1 and 4 (the forward
direction of openai/math's `exists_iff_order_one_or_four`; `exists_iff_of_circulantHadamard`,
`length_le_thirteen_of_circulantHadamard`). Both hypotheses are stated as openai/math states them, so its two
theorems discharge them by unfolding alone.

Not claimed: the even-length classification and the circulant Hadamard theorem themselves (openai/math catalogues
Lean proofs of both, at Lean v4.34.1, not registered on Palomar and not checked here); Turyn–Storer's Theorem 1;
the uniqueness of the sequences. <!-- DESK: if `unique` lands, move it to the bullets and count fourteen. -->

> As of 2026-10-09 (UTC), no formalization of the odd-length classification was located in openai/math (whose
> scope note for family 179 leaves the odd lengths out), the Palomar registry, formal-conjectures (which states
> the Barker conjecture, length at most 13, as open), Mathlib, the Isabelle AFP, Lean Pool, Hexagon, the Lean
> Zulip, or GitHub's Lean code.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by the
committed manifest; there are no GitHub Actions workflows. `python scripts/verify.py --fetch-cache` runs every
check (the pins, the source guard, the definition comparison against openai/math, the statement comparison, the
build with the axiom audit, module resolution, the elaboration check of the seven definitions, and Palomar's
core-notation audit); [VERIFICATION.md](VERIFICATION.md) lists them and their limits, [PROOF.md](PROOF.md) gives the
mathematics with the Lean name of every step, and [DISCLOSURE.md](DISCLOSURE.md) the assistance statement.

License: [MIT](LICENSE); the restated definitions and the adapted parts named in NOTICE derive from Apache-2.0
work of OpenAI ([NOTICE](NOTICE), [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt)).
