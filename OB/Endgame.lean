module

public import OB.Runs

/-!
# The endgame, the alternation, and the classification

From `run_bounds_seq` with `p, q` odd, `3 ≤ p < q`, `p ∤ q`: `2q - 3 ≤ n ≤ p + q + 1` gives
`q ∈ {p + 2, p + 4}`.

* `q = p + 2`: `n ∈ {2p + 1, 2p + 3}`. `doubling_seq` at `u = p - 1` says position `2p - 2` is not a
  change (`p - 1` is not), so by `skew_pair` position `n - 2p + 2` is a change: `3` (when
  `n = 2p + 1`), so `p ∣ 3`, `p = 3`, `n = 7`; or `5` (when `n = 2p + 3`), so `p ∣ 5` or `5 = q`,
  i.e. `p ∈ {3, 5}`: `p = 5` gives `n = 13`; `p = 3` gives `n = 9`, where `doubling_seq` at `u = 3`
  makes `6` a change while `skew_pair` at `s = 3` says `6 = 9 - 3` is not.
* `q = p + 4`: `n = 2p + 5`; exactly one of `p + 2`, `p + 3` is a change (`skew_pair`,
  `(p + 2) + (p + 3) = n`), both are `< q`, so `p` divides it: `p ∣ p + 3`, `p = 3`, `n = 11`.

So `n ∈ {7, 11, 13}` (`endgame`). The alternation `alt h j = (-1)^j h j` multiplies `C(k)` by
`(-1)^k` and so preserves `IsBarker`; it makes `h 0 = h 1` hold. With `p`, `q` from `Nat.find`
(`exists_q` and `skew_pair` at `s = 1` for the first change), `odd_length_mem_internal` follows for
`n ≥ 7`; `n ≤ 5` is in the list.

Lane: **endgame**.
-/

@[expose] public section

open Finset

namespace OddBarker

theorem endgame {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- The alternation `j ↦ (-1)^j h j`. -/
def alt {n : ℕ} (h : Fin n → ℤ) : Fin n → ℤ := fun j => (-1) ^ j.val * h j

theorem aperiodic_alt {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic (alt h) k = (-1) ^ k * aperiodic h k := by
  sorry

theorem isBarker_alt {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) : IsBarker (alt h) := by
  sorry

/-- The Challenge's `odd_length_mem`. -/
theorem odd_length_mem_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

end OddBarker
