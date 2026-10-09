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

/-- For `1 ≤ s < n`: `s` is a sign change iff `d s = -1`. -/
theorem en_change_iff {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s ≠ seq h (s - 1) ↔ seq h (s - 1) * seq h s = -1 := by
  rcases seq_sign hb.1 (show s - 1 < n by omega) with h1 | h1 <;>
    rcases seq_sign hb.1 hsn with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- For `1 ≤ s < n`: `d s = 1 ∨ d s = -1`. -/
theorem en_d_sign {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h (s - 1) * seq h s = 1 ∨ seq h (s - 1) * seq h s = -1 := by
  rcases seq_sign hb.1 (show s - 1 < n by omega) with h1 | h1 <;>
    rcases seq_sign hb.1 hsn with h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem endgame {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    n = 7 ∨ n = 11 ∨ n = 13 := by
  obtain ⟨hpo, hqo, hq2, hnpq⟩ :=
    run_bounds_seq hb hn h7 h01 hpn hpB hpmin hqn hqB hpq hqmin
  have hp2 := two_le_p h01 hpB
  have hplq := p_lt_q hpB hpmin hqB hpq hp2
  have hn' := hn
  obtain ⟨a, ha⟩ := hpo
  obtain ⟨b, hb'⟩ := hqo
  obtain ⟨c, hc⟩ := hn'
  have hp3 : 3 ≤ p := by omega
  have hcase : (q = p + 2 ∧ (n = 2 * p + 1 ∨ n = 2 * p + 3)) ∨ (q = p + 4 ∧ n = 2 * p + 5) := by
    omega
  rcases hcase with ⟨hq, hn2⟩ | ⟨hq, hn2⟩
  · -- `q = p + 2`: position `2p - 2` is not a change, so `n - 2p + 2` is.
    have hdbl := doubling_seq hb hn (u := p - 1) (by omega) (by omega)
    have hsk := skew_pair hb hn (s := 2 * (p - 1)) (by omega) (by omega)
    have hpm := hpmin (p - 1) (by omega) (by omega)
    rw [hpm, seq_mul_self hb.1 (by omega)] at hdbl
    have hd : seq h (n - 2 * (p - 1) - 1) * seq h (n - 2 * (p - 1)) = -1 := by linarith
    have hch := (en_change_iff hb (s := n - 2 * (p - 1)) (by omega) (by omega)).mpr hd
    rcases hn2 with hn2 | hn2
    · have hdv := hqmin _ (by omega) (by omega) hch
      rw [show n - 2 * (p - 1) = 3 by omega] at hdv
      have := Nat.le_of_dvd (by norm_num) hdv
      omega
    · by_cases hp5 : p = 3
      · exfalso
        subst hp5
        have hdb3 := doubling_seq hb hn (u := 3) (by norm_num) (by omega)
        have hsk3 := skew_pair hb hn (s := 3) (by norm_num) (by omega)
        rw [show n - 3 - 1 = 2 * 3 - 1 by omega, show n - 3 = 2 * 3 by omega] at hsk3
        have hz : seq h (2 * 3 - 1) * seq h (2 * 3) = 0 := by linarith
        rcases seq_sign hb.1 (show 2 * 3 - 1 < n by omega) with e1 | e1 <;>
          rcases seq_sign hb.1 (show 2 * 3 < n by omega) with e2 | e2 <;>
          rw [e1, e2] at hz <;> norm_num at hz
      · have hdv := hqmin _ (by omega) (by omega) hch
        rw [show n - 2 * (p - 1) = 5 by omega] at hdv
        have := Nat.le_of_dvd (by norm_num) hdv
        omega
  · -- `q = p + 4`, `n = 2p + 5`: one of `p + 2`, `p + 3` is a change.
    have hsk := skew_pair hb hn (s := p + 3) (by omega) (by omega)
    rw [show n - (p + 3) - 1 = p + 2 - 1 by omega, show n - (p + 3) = p + 2 by omega] at hsk
    rcases en_d_sign hb (s := p + 2) (by omega) (by omega) with hd | hd
    · have hd3 : seq h (p + 3 - 1) * seq h (p + 3) = -1 := by rw [hsk, hd]
      have hch := (en_change_iff hb (s := p + 3) (by omega) (by omega)).mpr hd3
      have hdv := hqmin _ (by omega) (by omega) hch
      have h3 := (Nat.dvd_add_right (dvd_refl p)).mp hdv
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have hch := (en_change_iff hb (s := p + 2) (by omega) (by omega)).mpr hd
      have hdv := hqmin _ (by omega) (by omega) hch
      have h2 := (Nat.dvd_add_right (dvd_refl p)).mp hdv
      have := Nat.le_of_dvd (by norm_num) h2
      omega

/-- The alternation `j ↦ (-1)^j h j`. -/
def alt {n : ℕ} (h : Fin n → ℤ) : Fin n → ℤ := fun j => (-1) ^ j.val * h j

theorem en_seq_alt {n : ℕ} (h : Fin n → ℤ) (i : ℕ) : seq (alt h) i = (-1) ^ i * seq h i := by
  unfold seq
  split_ifs with hi
  · simp [alt]
  · simp

theorem aperiodic_alt {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic (alt h) k = (-1) ^ k * aperiodic h k := by
  rw [aperiodic_eq_sum, aperiodic_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [en_seq_alt, en_seq_alt, pow_add]
  have h2 : ((-1 : ℤ) ^ j) * (-1) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (seq h j * seq h (j + k) * (-1) ^ k) * h2

theorem isBarker_alt {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) : IsBarker (alt h) := by
  refine ⟨fun j => ?_, fun k hk0 hkn => ?_⟩
  · rcases hb.1 j with h1 | h1 <;> rcases neg_one_pow_eq_or ℤ j.val with h2 | h2 <;>
      simp [alt, IsSign, h1, h2]
  · rw [aperiodic_alt, abs_mul, abs_neg_one_pow, one_mul]
    exact hb.2 k hk0 hkn

/-- The endgame from `seq g 0 = seq g 1`, with `p`, `q` found by `Nat.find`. -/
theorem en_of_h01 {n : ℕ} (g : Fin n → ℤ) (hn : Odd n) (hg : IsBarker g) (h7 : 7 ≤ n)
    (h01 : seq g 0 = seq g 1) : n = 7 ∨ n = 11 ∨ n = 13 := by
  have hex : ∃ s, 0 < s ∧ s < n ∧ seq g s ≠ seq g (s - 1) := by
    refine ⟨n - 1, by omega, by omega, ?_⟩
    have hs := skew_pair hg hn (s := 1) le_rfl (by omega)
    rw [show (1 : ℕ) - 1 = 0 from rfl, h01, seq_mul_self hg.1 (show 1 < n by omega)] at hs
    exact (en_change_iff hg (s := n - 1) (by omega) (by omega)).mpr (by linarith)
  obtain ⟨p, ⟨hp0, hpn, hpB⟩, hpm⟩ :
      ∃ p, (0 < p ∧ p < n ∧ seq g p ≠ seq g (p - 1)) ∧
        ∀ m, m < p → ¬ (0 < m ∧ m < n ∧ seq g m ≠ seq g (m - 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hpmin : ∀ s, 0 < s → s < p → seq g s = seq g (s - 1) := by
    intro s hs0 hsp
    by_contra hne
    exact hpm s hsp ⟨hs0, by omega, hne⟩
  have hp2 := two_le_p h01 hpB
  have hpo := p_odd hg hn h7 hpn hpB hpmin hp2
  have hp3 : 3 ≤ p := by obtain ⟨c, hc⟩ := hpo; omega
  have hexq := exists_q hg hn h7 hpn hpB hpmin hp3
  obtain ⟨q, ⟨hq0, hqn, hqB, hpq⟩, hqm⟩ :
      ∃ q, (0 < q ∧ q < n ∧ seq g q ≠ seq g (q - 1) ∧ ¬ p ∣ q) ∧
        ∀ m, m < q → ¬ (0 < m ∧ m < n ∧ seq g m ≠ seq g (m - 1) ∧ ¬ p ∣ m) :=
    ⟨Nat.find hexq, Nat.find_spec hexq, fun m hm => Nat.find_min hexq hm⟩
  have hqmin : ∀ s, 0 < s → s < q → seq g s ≠ seq g (s - 1) → p ∣ s := by
    intro s hs0 hsq hne
    by_contra hnd
    exact hqm s hsq ⟨hs0, by omega, hne, hnd⟩
  exact endgame hg hn h7 h01 hpn hpB hpmin hqn hqB hpq hqmin

/-- The Challenge's `odd_length_mem`. -/
theorem odd_length_mem_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  by_cases h7 : n < 7
  · obtain ⟨c, hc⟩ := hn
    omega
  push Not at h7
  have hor : seq h 0 = seq h 1 ∨ seq (alt h) 0 = seq (alt h) 1 := by
    rw [en_seq_alt, en_seq_alt]
    rcases seq_sign hb.1 (show 0 < n by omega) with e0 | e0 <;>
      rcases seq_sign hb.1 (show 1 < n by omega) with e1 | e1 <;> rw [e0, e1] <;> norm_num
  have key : n = 7 ∨ n = 11 ∨ n = 13 := by
    rcases hor with e | e
    · exact en_of_h01 h hn hb h7 e
    · exact en_of_h01 (alt h) hn (isBarker_alt hb) h7 e
  rcases key with e | e | e <;> omega

end OddBarker
