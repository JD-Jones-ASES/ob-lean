module

public import OB.Fold
public import OB.KeyBound

/-!
# The run structure (Schmidt–Willms, Lemmas 3 and 4)

`a = seq h`, `n` odd, `n ≥ 7`, `a 0 = a 1`. A *sign change* is a position `s ≥ 1` with
`a s ≠ a (s - 1)`; `p` is the least one (`s₁` of the paper, the length of the first run) and `q` the
least one not divisible by `p` (`s_e`). Everything below uses only `skew_pair`, `doubling_seq` and
the signs:

* `2 ≤ p` (from `a 0 = a 1`); `2p ≤ n + 1` (`skew_pair` at `s = p - 1`: positions `1, …, p - 1` are
  not changes, so `n - 1, …, n - p + 1` are, and `n - p + 1 ≥ p`); `p` odd (`doubling_seq` at
  `u = p/2` would make `p/2` a change); so `3 ≤ p`;
* a change not divisible by `p` exists: `n - 1` and `n - 2` are changes (`skew_pair` at `s = 1, 2`)
  and `p ≥ 3` divides at most one of them (`exists_q`);
* `p < q`; `2q ≤ n + 3`: otherwise the windows `[1, q)` and `(n - q, n)` overlap in three consecutive
  positions `s, s + 1, s + 2`, each a change iff divisible by `p` (prefix) and a change iff `n - s`
  is not (`skew_pair`), so two of `n - s, n - s - 1, n - s - 2` are multiples of `p ≥ 3`;
  `q` odd (`doubling_seq` at `u = q/2`);
* `n ≤ p + q + 1` (`key_bound` with `fold_seq` at `p + q - 2` and `p + q`, if `p + q + 3 ≤ n`).

Lane: **runs**.
-/

@[expose] public section

open Finset

namespace OddBarker

theorem two_le_p {n : ℕ} {h : Fin n → ℤ} (h01 : seq h 0 = seq h 1) {p : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) : 2 ≤ p := by
  sorry

theorem two_mul_p_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    2 * p ≤ n + 1 := by
  sorry

theorem p_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    Odd p := by
  sorry

/-- A sign change not divisible by `p` exists (`n - 1` or `n - 2`). -/
theorem exists_q {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p) :
    ∃ s, 0 < s ∧ s < n ∧ seq h s ≠ seq h (s - 1) ∧ ¬ p ∣ s := by
  sorry

theorem p_lt_q {n : ℕ} {h : Fin n → ℤ} {p q : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q) (hp2 : 2 ≤ p) : p < q := by
  sorry

theorem two_mul_q_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    2 * q ≤ n + 3 := by
  sorry

theorem q_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hq : 2 * q ≤ n + 3) :
    Odd q := by
  sorry

/-- Lemma 4: `n ≤ p + q + 1`. -/
theorem n_le_p_add_q_add_one {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) (hpodd : Odd p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hqodd : Odd q) (hplq : p < q) :
    n ≤ p + q + 1 := by
  sorry

/-- The run bounds on `ℕ`. -/
theorem run_bounds_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  sorry

/-- The Challenge's `run_bounds`. -/
theorem run_bounds_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (h7 : 7 ≤ n)
    (h01 : h ⟨0, by omega⟩ = h ⟨1, by omega⟩) (p q : ℕ)
    (hpn : p < n) (hpB : h ⟨p, hpn⟩ ≠ h ⟨p - 1, by omega⟩)
    (hpmin : ∀ s (hs0 : 0 < s) (hsp : s < p), h ⟨s, by omega⟩ = h ⟨s - 1, by omega⟩)
    (hqn : q < n) (hqB : h ⟨q, hqn⟩ ≠ h ⟨q - 1, by omega⟩) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s (hs0 : 0 < s) (hsq : s < q), h ⟨s, by omega⟩ ≠ h ⟨s - 1, by omega⟩ → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  sorry

end OddBarker
