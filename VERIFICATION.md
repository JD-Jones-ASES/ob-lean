# Verification

All fourteen statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the module-resolution check, the elaboration check and Palomar's core-notation
audit of the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks
below were last run on the tree of the final commit; a build log is evidence for that tree only. Theorems are
numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no
`definition_names`: a name there is a definition hole whose value the Solution supplies; the eight definitions
here are fully specified in the Challenge, so the comparator checks the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `odd_length_mem` — odd `n`, Barker ⇒ `n ∈ {1, 3, 5, 7, 11, 13}` | OB/Endgame.lean (with Runs, Fold, Skew, Parity) |
| 2 | `odd_exists_iff` — odd `n`: a Barker sequence of length `n` exists iff `n ∈ {1, 3, 5, 7, 11, 13}` | OB/Compose.lean (with Endgame, Witnesses) |
| 3 | `unique` — odd `n`: a Barker sequence is `±canon n` or `±(−1)^j canon n` | OB/Unique.lean (with Endgame) |
| 4 | `aperiodic_eq` — odd `n`: `C(k) = 0` for odd `k`, `(−1)^((n−1)/2)` for even `k` | OB/Parity.lean |
| 5 | `skew` — `h k · h (n−1−k) = (−1)^((n−1)/2 + k)` | OB/Skew.lean |
| 6 | `fold` — `∑_{k ≤ w} (−1)^k h k · h (w−k) = 1` for even `w ≤ n − 3` | OB/Fold.lean |
| 7 | `doubling` — `h (u−1) · h u = h (2u−1) · h (2u)` for `1 ≤ u ≤ (n−3)/2` | OB/Fold.lean |
| 8 | `run_bounds` — `p`, `q` odd, `2q − 3 ≤ n ≤ p + q + 1` (Schmidt–Willms, Lemmas 3 and 4) | OB/Runs.lean (with KeyBound, Identity) |
| 9 | `four_dvd_of_even` — even `n > 2`, Barker ⇒ `4 ∣ n` | OB/Hadamard.lean (with Parity) |
| 10 | `existsRealCirculantHadamard_of_even` — even `n > 2`, Barker ⇒ a real circulant Hadamard matrix of order `n` | OB/Hadamard.lean |
| 11 | `exists_iff_of_even` — given the even half, Barker lengths are exactly `{1, 2, 3, 4, 5, 7, 11, 13}` | OB/Compose.lean |
| 12 | `length_le_thirteen_of_even` — given the even half, every Barker sequence has length `≤ 13` | OB/Compose.lean |
| 13 | `exists_iff_of_circulantHadamard` — the same classification, given the circulant Hadamard statement | OB/Hadamard.lean (with Compose) |
| 14 | `length_le_thirteen_of_circulantHadamard` — length `≤ 13`, given the circulant Hadamard statement | OB/Hadamard.lean (with Compose) |

Each statement is restated verbatim in Solution.lean and closed by the internal theorem of the same name with the
suffix `_internal`. The hypotheses of theorems 11–14 are not proved here: `heven` is the statement
`OAI.CirculantHadamard.Barker.even_length_eq_two_or_four` of openai/math with its binders, and `hcirc` the forward
direction of `OAI.CirculantHadamard.exists_iff_order_one_or_four`; since the seven definitions are openai/math's
character for character, those theorems, in one environment with these, discharge the hypotheses by unfolding.
PROOF.md names the lemma behind each step.

## Local checks

```sh
python scripts/verify.py --fetch-cache
```

runs, in order: the pins (`lean-toolchain` and the Mathlib revision of `lake-manifest.json` are the committed ones),
`scripts/check-source.py`, `scripts/check_definitions.py`, `scripts/check_statements.py`, `scripts/check_barker.py`, the metadata check (formalization.yaml parses; its
title length, main results and alignment; `comparator.json` lists no definition holes), `lake build` of the four
targets `OB`, `Challenge`, `Solution`, `Test`, `lake env python scripts/check_module_resolution.py`, the elaboration
check (every compared definition printed with `pp.all` from the Challenge and from `OB.Defs`; the outputs must be
identical), and Palomar's `scripts/core_notation_audit.lean` on the twenty-two declarations of the statement surface (the
fourteen compared theorems of `comparator.json` and the eight definitions); the last line is `VERIFY: PASS` or `VERIFY: FAIL`.
`--skip-build` leaves out the four Lean steps.

The `Test` target imports `Solution` and audits every constant of its environment whose name begins with
`OddBarker.`, `_private.OB.` or `_private.Solution.` (190 constants on the tree of the final commit; the audit fails below 80),
permits only `propext`, `Classical.choice` and `Quot.sound`, and fails if any of the fourteen compared theorems is
missing. A placeholder in a proof compiles with a warning; this audit is what fails the build. Challenge.lean
intentionally contains fourteen proof placeholders; Solution.lean and the modules it imports contain none, and
Solution.lean does not import Challenge.lean. The source guard rejects `sorry`, `sorryAx`, `admit`, `axiom`,
`unsafe`, `partial`, `native_decide`, `implemented_by`, `extern`, `Lean.ofReduceBool` and the kernel-bypass options
`debug.skipKernelTC` and `debug.byAsSorry` in `OB/`, Solution.lean and `Test/`, the same tokens except `sorry` in
Challenge.lean, and any `debug.` option in the `[leanOptions]` table of lakefile.toml. `check_definitions.py` compares the
eight definitions of Challenge.lean and `OB/Defs.lean` character for character with each other and, for the seven
restated ones, up to the namespace, with `lean/ComparatorChallenges/EvenBarker.lean` (`IsSign`, `aperiodic`, `IsBarker`) and
`lean/ComparatorChallenges/CirculantHadamard.lean` (`RealMatrix`, `IsCirculant`, `IsSignHadamard`,
`ExistsRealCirculantHadamard`) of openai/math at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, whose copies are
kept in `scripts/` as reference data; `check_statements.py` compares every theorem header of Challenge.lean with
Solution.lean. Palomar's `scripts/core_notation_audit.lean` is a copy from github.com/PalomarRegistry/PalomarSubmission (MIT; see
NOTICE), unmodified apart from a three-line provenance comment at its head.
The core-notation audit needs about 4 GB of memory and a few minutes; run it with no other Lean process active. The source guard
covers the eighteen proof files (`OB/*.lean`, `OB.lean`, `Solution.lean`, `Test.lean`, `Test/Axioms.lean`), Challenge.lean and the lakefile options.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by the
committed manifest; `lake update` is never run. Every `.lean` file of the repository carries a `module` header.
`OB/Defs.lean` imports exactly what the Challenge imports (`Mathlib`), so that the eight definitions elaborate to
identical terms in both environments. A build of the four targets from an empty `.lake/build` after `lake exe cache get` takes about five minutes on a
16 GB desktop (each module 13–30 s); `python scripts/verify.py` about ten.

## The finite computations

There is no `native_decide`, and the classification enumerates no sequences: `n = 9` is excluded by the argument
(PROOF.md, the endgame). The kernel computations are the eight witnesses, each `IsBarker` by `decide` over its
signs and its at most twelve shifts; the control `forged13_not_isBarker` (the length-13 sequence with its last
sign flipped has `C(1) = 2`), which is a theorem, so a forged witness is rejected by construction; and the
uniqueness theorem's six enumerations `un_check1 … un_check13` (`decide +kernel` over every `±1` list of length
`n`, `2ⁿ` lists, 8,192 at `n = 13`: each list that passes the list form of the Barker test is one of the four
listed sequences; about 30 s for the module). Everything else is
`omega` over residues and divisibility, `ring`/`linear_combination` identities, and big-operator rewriting.
`scripts/check_barker.py` (Python 3.9+, standard library, under a minute) is a cross-check no Lean proof depends on:
an outside-in exhaustive search of every `±1` sequence of length 1 to 45 (lengths 1, 2, 3, 4, 5, 7, 11, 13 with
2, 4, 4, 8, 4, 4, 4, 4 sequences; a plain `2ⁿ` enumeration agrees to `n = 16`), the statements `aperiodic_eq`,
`skew`, `fold`, `doubling` and `run_bounds` evaluated as written on every odd sequence found, the circulant Gram
check on the even ones, forged controls (every check fails on some single-sign flip), and the observation that
sequences satisfying only `skew` and `fold` exist for odd `n ≤ 61` exactly at the six lengths, where they are the
Barker sequences; `scripts/README-check_barker.md` says what it does and does not certify.

## Not checked here

- The even-length classification (`even_length_eq_two_or_four`) and the circulant Hadamard theorem
  (`exists_iff_order_one_or_four`) are hypotheses. openai/math catalogues Lean proofs of both at Lean v4.34.1; they
  are not registered on Palomar, and nothing of them is built or checked here.
- Turyn–Storer's Theorem 1 and their inductive route are not formalized; the proof formalized is Schmidt–Willms's,
  recast (PROOF.md).
