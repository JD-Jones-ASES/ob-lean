module

public import OB.Parity

/-!
# Skew-symmetry (Schmidt–Willms, Lemma 2(i))

With `a = seq h`, the product `∏_{j < n - u} a j a (j + u)` is read off the autocorrelation
(`prod_signs`), and two consecutive shifts `u`, `u + 1` share every factor except `a u` and
`a (n - 1 - u)`; since one of the two shifts is odd (autocorrelation `0`) and the other even
(autocorrelation `(-1)^((n-1)/2)`), `a k * a (n - 1 - k) = (-1)^((n-1)/2 + k)` for every `k < n`
(`skew_seq`). The sign-change form `skew_pair`: with `d s = a (s - 1) a s`, `d s = -d (n - s)` for
`1 ≤ s ≤ n - 1` (position `s` is a sign change iff position `n - s` is not).

Lane: **skew**.
-/

@[expose] public section

open Finset

namespace OddBarker

/-- The product of the terms of `C(u)` is `1 - (((n - u) - C(u)) % 4)`. -/
theorem prod_shift_eq {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {u : ℕ} (hun : u ≤ n) :
    ∏ j ∈ range (n - u), seq h j * seq h (j + u)
      = 1 - ((((n - u : ℕ) : ℤ) - aperiodic h u) % 4) := by
  have hx : ∀ i ∈ range (n - u),
      seq h i * seq h (i + u) = 1 ∨ seq h i * seq h (i + u) = -1 := by
    intro i hi
    have hi1 : i < n := by simp at hi; omega
    have hi2 : i + u < n := by simp at hi; omega
    rcases seq_sign hs hi1 with h1 | h1 <;> rcases seq_sign hs hi2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [(prod_signs (range (n - u)) (fun j => seq h j * seq h (j + u)) hx).1, card_range,
    ← aperiodic_eq_sum]

/-- Consecutive shifts share all factors but two. -/
theorem sk_prod_split {n : ℕ} (h : Fin n → ℤ) {u : ℕ} (hu : u + 1 ≤ n) :
    ∏ j ∈ range (n - u), seq h j * seq h (j + u)
      = (∏ j ∈ range (n - (u + 1)), seq h j * seq h (j + (u + 1)))
          * (seq h (n - 1 - u) * seq h u) := by
  have he : n - u = (n - (u + 1)) + 1 := by omega
  have h1 : n - (u + 1) = n - 1 - u := by omega
  have hA : ∏ j ∈ range (n - u), seq h j
      = (∏ j ∈ range (n - (u + 1)), seq h j) * seq h (n - 1 - u) := by
    rw [he, prod_range_succ, h1]
  have hB : ∏ j ∈ range (n - u), seq h (j + u)
      = (∏ j ∈ range (n - (u + 1)), seq h (j + (u + 1))) * seq h u := by
    rw [he, prod_range_succ']
    simp only [zero_add]
    congr 1
    apply prod_congr rfl
    intro j _
    congr 1
    omega
  rw [prod_mul_distrib, prod_mul_distrib, hA, hB]
  ring

theorem sk_neg_one_pow (x : ℕ) :
    ((-1 : ℤ) ^ x = 1 ∧ x % 2 = 0) ∨ ((-1 : ℤ) ^ x = -1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd x with hx | hx
  · exact Or.inl ⟨hx.neg_one_pow, Nat.even_iff.mp hx⟩
  · exact Or.inr ⟨hx.neg_one_pow, Nat.odd_iff.mp hx⟩

/-- Skew-symmetry away from the last index. -/
theorem sk_skew_lt {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : k + 1 < n) :
    seq h k * seq h (n - 1 - k) = (-1) ^ ((n - 1) / 2 + k) := by
  have hsplit := sk_prod_split h (u := k) (by omega)
  have hP1 := prod_shift_eq hb.1 (u := k + 1) (by omega)
  have hC1 := aperiodic_eq_internal h hn hb (k + 1) (by omega) (by omega)
  have hsg : seq h (n - 1 - k) * seq h k = 1 ∨ seq h (n - 1 - k) * seq h k = -1 := by
    rcases seq_sign hb.1 (i := n - 1 - k) (by omega) with h1 | h1 <;>
      rcases seq_sign hb.1 (i := k) (by omega) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rw [hP1] at hsplit
  rw [mul_comm]
  obtain ⟨q0, hP0, hq0⟩ : ∃ q, ∏ j ∈ range (n - k), seq h j * seq h (j + k) = q ∧
      ((k = 0 ∧ q = 1) ∨ (0 < k ∧ q = 1 - ((((n - k : ℕ) : ℤ) - aperiodic h k) % 4) ∧
        aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0)) := by
    rcases Nat.eq_zero_or_pos k with h0 | hk0
    · subst h0
      refine ⟨1, ?_, Or.inl ⟨rfl, rfl⟩⟩
      apply prod_eq_one
      intro j hj
      simp at hj
      simpa using seq_mul_self hb.1 hj
    · exact ⟨_, prod_shift_eq hb.1 (by omega), Or.inr ⟨hk0, rfl,
        aperiodic_eq_internal h hn hb k hk0 (by omega)⟩⟩
  rw [hP0] at hsplit
  generalize seq h (n - 1 - k) * seq h k = s at hsplit hsg ⊢
  generalize aperiodic h k = c0 at hq0
  generalize aperiodic h (k + 1) = c1 at hsplit hC1
  obtain ⟨t, rfl⟩ := hn
  have ht2 : (2 * t + 1 - 1) / 2 = t := by omega
  rw [ht2] at hq0 hC1 ⊢
  simp only [Nat.even_iff] at hq0 hC1
  rcases sk_neg_one_pow t with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;>
  rcases sk_neg_one_pow (t + k) with ⟨e2, p2⟩ | ⟨e2, p2⟩ <;>
  rw [e1] at hq0 hC1 <;> rw [e2] <;>
  split_ifs at hq0 hC1 <;> rcases hsg with rfl | rfl <;> omega

/-- Skew-symmetry on `ℕ`: for odd `n`, a Barker sequence and `k < n`,
`a k * a (n - 1 - k) = (-1)^((n - 1)/2 + k)`. -/
theorem skew_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ} (hk : k < n) :
    seq h k * seq h (n - 1 - k) = (-1) ^ ((n - 1) / 2 + k) := by
  rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
  · exact sk_skew_lt hb hn hk1
  · have hkn : k = n - 1 := by omega
    rcases Nat.eq_zero_or_pos k with h0 | hk0
    · subst h0
      have hn1 : n = 1 := by omega
      subst hn1
      show seq h 0 * seq h 0 = (-1) ^ 0
      rw [pow_zero]
      exact seq_mul_self hb.1 (by norm_num)
    · have h0 := sk_skew_lt hb hn (k := 0) (by omega)
      have e : n - 1 - k = 0 := by omega
      rw [e, mul_comm]
      have e' : n - 1 - 0 = k := by omega
      rw [e'] at h0
      rw [h0]
      obtain ⟨t, rfl⟩ := hn
      rw [pow_add, pow_add, pow_zero, (show Even k from ⟨t, by omega⟩).neg_one_pow]

/-- The Challenge's `skew`. -/
theorem skew_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : Fin n) :
    h k * h (Fin.rev k) = (-1) ^ ((n - 1) / 2 + k.val) := by
  have h1 : h k = seq h k.val := by rw [seq_eq h k.isLt]
  have h2 : h (Fin.rev k) = seq h (n - 1 - k.val) := by
    rw [seq_eq h (by omega)]
    congr 1
    ext
    simp only [Fin.val_rev]
    omega
  rw [h1, h2]
  exact skew_seq hb hn k.isLt

/-- Sign changes mirror with a flip: for `1 ≤ s ≤ n - 1`,
`a (s - 1) * a s = -(a (n - s - 1) * a (n - s))`. -/
theorem skew_pair {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s + 1 ≤ n) :
    seq h (s - 1) * seq h s = -(seq h (n - s - 1) * seq h (n - s)) := by
  have e1 := skew_seq hb hn (k := s - 1) (by omega)
  have e2 := skew_seq hb hn (k := s) (by omega)
  have r1 : n - 1 - (s - 1) = n - s := by omega
  have r2 : n - 1 - s = n - s - 1 := by omega
  rw [r1] at e1
  rw [r2] at e2
  have hp : (-1 : ℤ) ^ ((n - 1) / 2 + s) = -(-1) ^ ((n - 1) / 2 + (s - 1)) := by
    have : (n - 1) / 2 + s = (n - 1) / 2 + (s - 1) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [hp, ← e1] at e2
  rcases seq_sign hb.1 (i := s - 1) (by omega) with h1 | h1 <;>
  rcases seq_sign hb.1 (i := s) (by omega) with h2 | h2 <;>
  rcases seq_sign hb.1 (i := n - s - 1) (by omega) with h3 | h3 <;>
  rcases seq_sign hb.1 (i := n - s) (by omega) with h4 | h4 <;>
  rw [h1, h2, h3, h4] at e2 <;> rw [h1, h2, h3, h4] <;>
    (revert e2; norm_num)

end OddBarker
