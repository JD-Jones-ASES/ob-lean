# Architecture and lane protocol (working document; not part of the published repository)

## What this repository proves

A Barker sequence of length `n` is `h : Fin n → ℤ` with every `h j ∈ {1, -1}` and
`|C(k)| ≤ 1` for `0 < k < n`, where `C(k) = aperiodic h k = ∑_{j < n-k} h j * h (j+k)`. For odd `n`
such a sequence exists iff `n ∈ {1, 3, 5, 7, 11, 13}` (Turyn–Storer 1961; the proof formalized is
Schmidt–Willms 2016, arXiv:1501.06035, recast — see PROOF.md when written, and the module docstrings).
With OpenAI's even half (`even_length_eq_two_or_four`: even `n > 0` ⇒ `n ∈ {2, 4}`) as a hypothesis,
the full classification `{1, 2, 3, 4, 5, 7, 11, 13}`; with OpenAI's circulant Hadamard theorem
(`exists_iff_order_one_or_four`) as a hypothesis, the same, through the even reduction (even `n > 2`
Barker ⇒ `4 ∣ n` ⇒ a real circulant Hadamard matrix of order `n`).

Compared theorems (all in `Challenge.lean`; each is closed in `Solution.lean` by `<name>_internal`):

| # | Theorem | Content | Module (lane) |
| --- | --- | --- | --- |
| 1 | `odd_length_mem` | odd `n`, Barker ⇒ `n ∈ {1,3,5,7,11,13}` | Endgame (**endgame**) |
| 2 | `odd_exists_iff` | odd `n`: exists iff `n ∈ {…}` | Compose (**compose**) |
| 3 | `aperiodic_eq` | odd `n`: `C(k) = 0` (odd `k`), `(-1)^((n-1)/2)` (even `k`) | Parity (**parity**) |
| 4 | `skew` | `h k * h (rev k) = (-1)^((n-1)/2 + k)` | Skew (**skew**) |
| 5 | `fold` | `∑_{k ≤ w} (-1)^k h k h (w-k) = 1`, even `w ≤ n-3` | Fold (**fold**) |
| 6 | `doubling` | `h (u-1) h u = h (2u-1) h (2u)`, `1 ≤ u ≤ (n-3)/2` | Fold (**fold**) |
| 7 | `run_bounds` | `p, q` odd, `2q - 3 ≤ n ≤ p + q + 1` (Lemmas 3, 4) | Runs (**runs**) |
| 8 | `four_dvd_of_even` | even `n > 2` Barker ⇒ `4 ∣ n` | Hadamard (**hadamard**) |
| 9 | `existsRealCirculantHadamard_of_even` | even `n > 2` Barker ⇒ circulant Hadamard of order `n` | Hadamard (**hadamard**) |
| 10 | `exists_iff_of_even` | the full classification given the even half | Compose (**compose**) |
| 11 | `length_le_thirteen_of_even` | `n ≤ 13` given the even half | Compose (**compose**) |
| 12 | `exists_iff_of_circulantHadamard` | the full classification given circulant Hadamard | Hadamard (**hadamard**) |
| 13 | `length_le_thirteen_of_circulantHadamard` | `n ≤ 13` given circulant Hadamard | Hadamard (**hadamard**) |
| (14) | `unique` (stretch; added to the Challenge only if it closes) | odd `n`: `h = ±canon n` or `±alt (canon n)` | Unique (**unique**) |

## Module map and owners

| Module | Lane | Imports | Status |
| --- | --- | --- | --- |
| `OB/Defs` | desk | `Mathlib` (identical to the Challenge — the comparator compares elaborated terms) | done |
| `OB/Bridge` | desk (ported) | Defs | done: `seq`, `seq_eq`, `seq_of_le`, `aperiodic_eq_sum`, `prod_signs`, `seq_sign`, `seq_mul_self`, `aperiodic_parity`, `odd_shift_zero` |
| `OB/Identity` | desk (ported) | Defs | done: `T0`, `neg_one_pow_sub`, `T0_odd`, `T0_step` |
| `OB/KeyBound` | desk (ported) | Identity | done: `key_bound` (Lemma 4 in sign-change form) |
| `OB/Parity` | **parity** | Bridge | `aperiodic_add_aperiodic_sub_mod_four`, `even_shift_eq`, `aperiodic_eq_internal`, `even_shift_zero_of_even` |
| `OB/Skew` | **skew** | Parity | `prod_shift_eq`, `skew_seq`, `skew_internal`, `skew_pair` |
| `OB/Fold` | **fold** | Skew, Identity | `fold_seq`, `fold_internal`, `prod_prefix`, `doubling_seq`, `doubling_internal` |
| `OB/Runs` | **runs** | Fold, KeyBound | `two_le_p` … `run_bounds_internal` (ten statements) |
| `OB/Endgame` | **endgame** | Runs | `endgame`, `alt`, `aperiodic_alt`, `isBarker_alt`, `odd_length_mem_internal` |
| `OB/Witnesses` | **witnesses** | Defs | eight `IsBarker` witnesses + the forged control |
| `OB/Compose` | **compose** | Endgame, Witnesses | `odd_exists_iff_internal`, `exists_iff_of_even_internal`, `length_le_thirteen_of_even_internal` |
| `OB/Hadamard` | **hadamard** | Parity, Compose | the even reduction and the circulant composition (eleven statements) |
| `OB/Unique` | **unique** (stretch) | Compose | `canon`, `unique_internal` |
| `OB/Main`, `Solution`, `Test` | desk | all | glue; the axiom audit |

Every lane proves the sorried statements of its own module only, using the sorried statements of
the modules it imports as black boxes (they compile; the desk merges finished lanes into main and
into running lanes' worktrees when a signature changes). Helpers go in the lane's own module with a
lane prefix (`par_`, `sk_`, `fo_`, `ru_`, `en_`, `wi_`, `co_`, `ha_`, `un_`) so names never clash at the merge.

## The mathematics, module by module

**Conventions.** `a = seq h : ℕ → ℤ` (zero off `[0, n)`); `m = (n - 1)/2`; `d s = a (s-1) * a s` for
`s ≥ 1` (`d s = -1` iff `s` is a *sign change*); `T0 a w = ∑_{k ≤ w} (-1)^k a k a (w-k)`.

**Parity.** `C(u) + C(n-u) = ∑_{j<n} a j · a ((j+u) mod n)` (the periodic autocorrelation; split the
cyclic sum at `n - u`: `C(n-u) = ∑_{i<u} a i · a (i+n-u)`). For signs `x y ≡ x - y + 1 (mod 4)`, and
`∑_{j<n} (a j - a ((j+u) mod n)) = 0` since the shifted sum is a permutation (in range form:
`∑_{j<n-u} a j + ∑_{i<u} a (i+n-u) = ∑_{j<n} a j = ∑_{j<n-u} a (j+u) + ∑_{i<u} a i`), so
`C(u) + C(n-u) ≡ n (mod 4)`. Odd `n`: `C(n-u) = 0` when `n-u` is odd (`odd_shift_zero`), so for even
`u`, `C(u) ≡ n (mod 4)` with `|C(u)| ≤ 1` forces `C(u) = (-1)^m`. Even `n`: `C(k) ≡ n - k (mod 2)`
(`aperiodic_parity`) is even for even `k`, so `C(k) = 0`. Mathlib: `Finset.sum_range_add`,
`Finset.range_eq_Ico`, `Finset.sum_Ico_consecutive`, `Int.emod_emod_of_dvd`, `omega` on residues.

**Skew.** `P(u) := ∏_{j<n-u} a j · a (j+u) = 1 - (((n-u) - C(u)) % 4)` by `prod_signs` with
`aperiodic_eq_sum`. `P(u) = (∏_{j<n-u} a j)(∏_{j<n-u} a (j+u))` and `P(u+1)` likewise; the two share
`∏_{j<n-u-1} a j` and `∏_{j<n-u-1} a (j+u+1)` (squares are `1`), leaving `P(u) P(u+1) = a (n-1-u) · a u`
(`Finset.prod_range_succ`, `Finset.prod_range_succ'`, `Finset.prod_mul_distrib`). One of `u, u+1` is odd
(`C = 0`), the other even (`C = (-1)^m`); case on `n % 4`, `u % 4` with `omega`/`decide` to read off
`a u · a (n-1-u) = (-1)^(m+u)` for `u ≤ n-2`; `u = n-1` is `a (n-1) · a 0`, the `u = 0` case reflected
(`(-1)^(m+n-1) = (-1)^m` as `n-1` is even). `skew_pair`: `d s · d (n-s) = [a (s-1) a (n-s)]·[a s a (n-s-1)]
= (-1)^(m+s-1) (-1)^(m+s) = -1`, and `d (n-s)^2 = 1`.

**Fold.** `C(n-1-w) = ∑_{j ≤ w} a j · a (j+n-1-w)`; by `skew_seq` at `k = w-j`,
`a (j+n-1-w) = (-1)^(m+w-j) a (w-j)` (multiply the skew identity by `a (w-j)`), so
`C(n-1-w) = (-1)^(m+w) ∑_{j ≤ w} (-1)^j a j a (w-j) = (-1)^m T0 a w` (`w` even;
`(-1)^(w-j) = (-1)^w (-1)^j`, `neg_one_pow_sub`); and `C(n-1-w) = (-1)^m` (`even_shift_eq`), so
`T0 a w = 1`. `prod_prefix`: split `T0 a (2j)` as `2 ∑_{k<j} (-1)^k a k a (2j-k) + (-1)^j`
(`Finset.sum_range_reflect` on the upper half; the middle term `a j ^ 2 = 1`), so
`∑_{k<j} t_k = (1 - (-1)^j)/2` with `t_k = (-1)^k a k a (2j-k)` signs; `prod_signs` gives
`∏ t_k = 1 - ((j - ∑ t_k) % 4)`, which is `(-1)^(j(j-1)/2)` in both parities, and
`∏_{k<j} (-1)^k = (-1)^(j(j-1)/2)`, so `∏_{k<j} a k a (2j-k) = 1`, i.e. `∏_{i ≤ 2j} a i = a j`
(`Finset.prod_range_reflect`, `Finset.prod_range_succ`). `doubling_seq`: divide the prefix products at
`2u` and `2u-2`: `a (2u-1) a (2u) = a (u-1) a u`.

**Runs.** Read the docstring of `OB/Runs.lean`. Everything is `skew_pair` (`d s = -d (n-s)`),
`doubling_seq` (`d u = d (2u)` for `1 ≤ u`, `2u+3 ≤ n`), and `omega` over divisibility
(`Nat.dvd_sub'`, `Nat.dvd_add_right`, `Nat.le_of_dvd`). `n_le_p_add_q_add_one`: if `p + q + 3 ≤ n`
then `fold_seq` at `w = p+q-2` and `w = p+q` (both even, `≤ n-3`) feed `key_bound` with `a = seq h`
(signs on `[0, p+q]` from `seq_sign`; `p ∤ q`; the minimality hypotheses translate directly).

**Endgame.** Read the docstring of `OB/Endgame.lean`. `aperiodic_alt`: `(-1)^j (-1)^(j+k) = (-1)^k`
termwise (`pow_add`, `Even.neg_one_pow`). `odd_length_mem_internal`: `n ≤ 5` by `omega` on `Odd n`;
`n ≥ 7`: WLOG `seq h 0 = seq h 1` (else pass to `alt h`, Barker by `isBarker_alt`, with
`seq (alt h) 0 = seq (alt h) 1`); `p := Nat.find` of `∃ s, 0 < s ∧ s < n ∧ seq h s ≠ seq h (s-1)`
(`s = n-1` works: `skew_pair` at `s = 1` with `d 1 = 1`); `q := Nat.find` of `exists_q`; then `endgame`.

**Witnesses.** `decide` per shift: `refine ⟨?_, ?_⟩; · show ∀ j, a13 j = 1 ∨ a13 j = -1; decide;
· intro k hk0 hkn; interval_cases k <;> decide` (compiled at the bench 10-06).

**Compose.** `odd_exists_iff_internal`: `→` by `odd_length_mem_internal`; `←` by the witnesses
(`rcases` the disjunction, `subst`, `exact ⟨a7, a7_isBarker⟩`). `exists_iff_of_even_internal`:
`Nat.even_or_odd n`; even: `heven h hn he hb`; odd: `odd_length_mem_internal`; `←`: eight witnesses.

**Hadamard.** Read the docstring of `OB/Hadamard.lean`. `periodic_eq_aperiodic_add`: split
`∑ j : Fin n` at `a.val` (`Fin.sum_univ_add` after `Fin.cast`, or go through `seq` and `Finset.range`:
`periodic h a = ∑_{j<n} seq h j * seq h ((j + (n - a)) % n)`, split at `j < a`); `Fin.coe_sub_iff_le`,
`Fin.coe_sub_iff_lt`. `circ_isSignHadamard`: `Matrix.mul_apply`, `Matrix.transpose_apply`,
`(circ h * (circ h)ᵀ) i j = ∑ k, (h (k - i) : ℝ) * h (k - j)`; substitute `l = k - i`
(`Equiv.subRight`/`Fintype.sum_equiv`), `k - j = l - (j - i)` (`sub_sub_sub_cancel_right` in the
`AddCommGroup (Fin n)` with `NeZero n`), cast the integer sum (`Int.cast_sum`, `Int.cast_mul`), then
`periodic_zero`/`periodic_offpeak_zero`; `Matrix.smul_apply`, `Matrix.one_apply`. OpenAI's
`Barker/Wraparound.lean` and `PeriodicModFour.lean` show one route (adapt with a docstring notice, or
write your own).

**Unique (stretch).** From `odd_length_mem_internal` the six lengths; for each, `skew_internal` gives
`h (rev k) = (-1)^(m+k) h k` (times `h k ^ 2 = 1`), so `h` is a function of its first `m+1` values; encode
those as a `Nat < 2^(m+1)` and check by `decide +kernel` (a Mathlib-free leaf is fine; never
`native_decide`) that every code whose extension is Barker is `± canon`/`± alt canon`. Or any shorter
route. Kill: 2.5 h or a kernel check over 10 minutes; report what closed.

## Rules for lanes

1. Work only in your worktree (`C:/GitHub_Files/Claude-Repos/wt/ob-<lane>`, branch `desk/<lane>`); edit
   only your module; never push; never touch `Challenge.lean`, `Solution.lean` or another lane's module.
2. Build only through `bash scripts/lane-build.sh OB.<Module>` from the worktree root (two machine-wide
   slots; it waits for 2.5 GB free). Never run `lake build` or `lean` directly. At most two processes per lane.
3. The box block (vault ADR-039): read free memory before any job above ~500 MB and never start one below
   3 GB free; the box lock `C:/GitHub_Files/Claude-Repos/BOX-LOCK` for anything heavy; the KILL file
   `C:/GitHub_Files/Claude-Repos/Claude-Math-Station/bench/rt-065-odd-barker/KILL` stops every loop you
   write; nothing detached; scratch files in your worktree's `.scratch/`, never `/tmp`.
4. A pinned statement that is false or unprovable as stated: prove the nearest correct version under a
   new name, leave the pin sorried, and report it as the first line of your report.
5. Kernel only: `decide`, `decide +kernel`; never `native_decide`, `axiom`, `unsafe`, `partial`,
   `implemented_by`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`#print axioms` your
   theorems before reporting).
6. Grep `error` in the build log separately from the sorry warnings (`grep -v "declaration uses 'sorry'"`).
7. Lean v4.35.0-rc2 gotchas: `le_or_gt` (not `le_or_lt`); `Nat.dvd_sub` (no order hypothesis);
   `Finset.notMem_empty`; `push Not` (not `push_neg`); `(iterate n tac); tac2`; a section `variable`
   hypothesis is included only if mentioned or `include`d; omega has no dark shadow and dies on 8-way
   disjunction goals (pick the disjunct first); `set_option linter.unusedVariables false in` goes above
   the docstring.
8. Commit on your branch when a statement closes (`git add OB/<Module>.lean; git commit -m "..."`), and
   again at the end; report the final commit hash, the list of closed and open statements, and
   `#print axioms` output.
