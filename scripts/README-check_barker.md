# check_barker.py

`python3 scripts/check_barker.py` (Python 3.9 or later, standard library only, exact integers, under a minute) prints `VERDICT: PASS` and exits 0 only if every check below holds; any failure prints a `FAIL` line, `VERDICT: FAIL` and a nonzero exit.

- **Search.** Every Barker sequence of length 1 to 45, by an outside-in backtracking search, each one re-checked by recomputing every autocorrelation, and the sets for lengths up to 16 compared with a plain enumeration of all 2^n sequences: lengths 1, 2, 3, 4, 5, 7, 11, 13 with 2, 4, 4, 8, 4, 4, 4, 4 sequences. The eight witnesses in `OB/Witnesses.lean` are among them.
- **Statements.** On every odd Barker sequence found, `aperiodic_eq`, `skew`, `fold`, `doubling` and `run_bounds` as written in `Challenge.lean` (natural-number subtraction and divisibility included). On every even one of length > 2: 4 | n, and the circulant matrix satisfies H Hᵀ = nI.
- **Forged controls.** `+++++--++-+--` has C(1) = 2 and is rejected. Every single-sign flip of an odd Barker sequence that is not itself Barker fails the statement checks, and each check fails on some forged input, so none of them passes vacuously.
- **Abstraction.** For odd n up to 61, sequences satisfying only `skew` and `fold` exist only at n = 1, 3, 5, 7, 11, 13, and there they are exactly the Barker sequences. The search is capped at 120 s and prints UNKNOWN if it reaches the cap.

What the script does not do: it checks finitely many cases and the statements on them. It does not prove the theorem for all n. The proof is the Lean development, and the script only shows that the pinned statements are not false on the sequences that exist.
