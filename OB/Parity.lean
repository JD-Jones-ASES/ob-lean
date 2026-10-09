module

public import OB.Bridge

/-!
# Autocorrelations modulo four

For a sign sequence and `0 < u < n`, `C(u) + C(n - u)` is the periodic autocorrelation at shift `u`,
and `xy ≡ x - y + 1 (mod 4)` for signs gives `C(u) + C(n - u) ≡ n (mod 4)`
(`aperiodic_add_aperiodic_sub_mod_four`). For odd `n` and a Barker sequence this pins every
nontrivial autocorrelation: `0` at odd shifts, `(-1)^((n-1)/2)` at even ones (`aperiodic_eq_internal`).
For even `n`, even shifts vanish by parity alone (`even_shift_zero_of_even`); the Hadamard module uses
the mod-four congruence at `u = 2` to get `4 ∣ n`.

Lane: **parity**.
-/

@[expose] public section

open Finset

namespace OddBarker

/-- Split a range sum at `a`, with the tail indexed as `i + a`. -/
theorem pa_split (f : ℕ → ℤ) (a b : ℕ) :
    ∑ j ∈ range (a + b), f j = ∑ j ∈ range a, f j + ∑ i ∈ range b, f (i + a) := by
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm]

/-- `C(u) + C(n - u) ≡ n (mod 4)` for a sign sequence and `0 < u < n`. -/
theorem aperiodic_add_aperiodic_sub_mod_four {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j))
    {u : ℕ} (hu0 : 0 < u) (hun : u < n) :
    (4 : ℤ) ∣ aperiodic h u + aperiodic h (n - u) - n := by
  obtain ⟨v, hv⟩ : ∃ v, v = n - u := ⟨_, rfl⟩
  have hvu : n - v = u := by omega
  rw [← hv, aperiodic_eq_sum h u, aperiodic_eq_sum h v, ← hv, hvu]
  have h1 : (4 : ℤ) ∣ ∑ j ∈ range v,
      (seq h j * seq h (j + u) - seq h j + seq h (j + u) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    rcases seq_sign hs (show j < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show j + u < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  have h2 : (4 : ℤ) ∣ ∑ i ∈ range u,
      (seq h i * seq h (i + v) - seq h (i + v) + seq h i - 1) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rcases seq_sign hs (show i < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show i + v < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h1 h2
  have e1 := pa_split (seq h) v u
  have e2 := pa_split (seq h) u v
  rw [show v + u = n by omega] at e1
  rw [show u + v = n by omega] at e2
  omega

/-- For odd `n` and a Barker sequence, every even nontrivial shift has autocorrelation
`(-1)^((n-1)/2)`. -/
theorem even_shift_eq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = (-1) ^ ((n - 1) / 2) := by
  have hv : Odd (n - k) := by
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb2⟩ := hk
    exact ⟨a - b, by omega⟩
  have hz := odd_shift_zero hb hn (n - k) hv (by omega) (by omega)
  have hd := aperiodic_add_aperiodic_sub_mod_four hb.1 hk0 hkn
  rw [hz] at hd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨m, hm⟩ := hn
  have hm2 : (n - 1) / 2 = m := by omega
  rw [hm2]
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow]
    obtain ⟨t, ht⟩ := he
    omega
  · rw [ho.neg_one_pow]
    obtain ⟨t, ht⟩ := ho
    omega

/-- The Challenge's `aperiodic_eq`. -/
theorem aperiodic_eq_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 := by
  split_ifs with he
  · exact even_shift_eq hb hn he hk0 hkn
  · exact odd_shift_zero hb hn k (Nat.not_even_iff_odd.mp he) hk0 hkn

/-- For even `n` and a Barker sequence, every even nontrivial shift has autocorrelation `0`
(parity: `C(k) ≡ n - k ≡ 0 (mod 2)` and `|C(k)| ≤ 1`). -/
theorem even_shift_zero_of_even {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  have hp := aperiodic_parity hb.1 hkn.le
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb2⟩ := hk
  omega

end OddBarker
