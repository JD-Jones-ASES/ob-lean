module

public import OB.Defs

/-!
# The bridge to `ℕ`-indexed sequences

`seq h` reads `h : Fin n → ℤ` on `ℕ`, zero outside `[0, n)`; `aperiodic h k` becomes a `Finset.range`
sum; a product of signs is read off its sum (`prod_signs`); and, for odd `n`, odd shifts have
autocorrelation `0` (`odd_shift_zero`).
-/

@[expose] public section

open Finset

namespace OddBarker

/-- The sequence read on `ℕ`, zero outside `[0, n)`. -/
def seq {n : ℕ} (h : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then h ⟨i, hi⟩ else 0

theorem seq_eq {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : i < n) : seq h i = h ⟨i, hi⟩ := by
  simp [seq, hi]

theorem seq_of_le {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : n ≤ i) : seq h i = 0 := by
  simp [seq, not_lt.mpr hi]

theorem aperiodic_eq_sum {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic h k = ∑ j ∈ range (n - k), seq h j * seq h (j + k) := by
  unfold aperiodic
  rw [← Fin.sum_univ_eq_sum_range (fun j => seq h j * seq h (j + k)) (n - k)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : j.val < n := by omega
  have h2 : j.val + k < n := by omega
  simp [seq, h1, h2]

/-- A product of signs is `1 - ((card - sum) % 4)`, and `card - sum` is even. -/
theorem prod_signs (s : Finset ℕ) (x : ℕ → ℤ) (hx : ∀ i ∈ s, x i = 1 ∨ x i = -1) :
    ∏ i ∈ s, x i = 1 - (((s.card : ℤ) - ∑ i ∈ s, x i) % 4) ∧
      ((s.card : ℤ) - ∑ i ∈ s, x i) % 2 = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih1]
    rcases hx a (Finset.mem_insert_self a s) with h | h <;> rw [h] <;> push_cast <;> omega

theorem seq_sign {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i = 1 ∨ seq h i = -1 := by
  simpa [seq, hi, IsSign] using hs ⟨i, hi⟩

theorem seq_mul_self {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i * seq h i = 1 := by
  rcases seq_sign hs hi with h1 | h1 <;> rw [h1] <;> norm_num

/-- `2 ∣ C(k) - (n - k)` for a sign sequence (each term is `±1`). -/
theorem aperiodic_parity {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {k : ℕ} (hk : k ≤ n) :
    (2 : ℤ) ∣ aperiodic h k - ((n - k : ℕ) : ℤ) := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hs hj1 with h1 | h1 <;> rcases seq_sign hs hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simpa using hdvd

theorem odd_shift_zero {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (k : ℕ)
    (hk : Odd k) (hk0 : 0 < k) (hkn : k < n) : aperiodic h k = 0 := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hb.1 hj1 with h1 | h1 <;> rcases seq_sign hb.1 hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hdvd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ := hdvd
  have hc : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by push_cast [hkn.le]; ring
  rw [hc] at hd
  subst hu hv
  push_cast at hd
  omega

end OddBarker
