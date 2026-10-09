module

public import OB.Skew
public import OB.Identity

/-!
# The folded identity and the doubling law (Schmidt–Willms, Lemma 2(ii))

For odd `n`, a Barker sequence `a = seq h` and even `w ≤ n - 3`: the even shift `n - 1 - w ≥ 2` has
autocorrelation `(-1)^((n-1)/2)`, and rewriting `a (j + n - 1 - w) = (-1)^((n-1)/2 + w - j) a (w - j)`
by skew-symmetry turns it into `(-1)^((n-1)/2) T0 a w`; so `T0 a w = 1` (`fold_seq`). Splitting
`T0 a (2j)` at its middle term gives `∑_{k < j} (-1)^k a k a (2j - k) = (1 - (-1)^j)/2`, and counting
signs (`prod_signs`) gives `∏_{k < j} a k a (2j - k) = 1`, i.e. `∏_{i ≤ 2j} a i = a j` (`prod_prefix`);
two consecutive `j` give `a (u - 1) a u = a (2u - 1) a (2u)` for `1 ≤ u ≤ (n - 3)/2` (`doubling_seq`).

Lane: **fold**.
-/

@[expose] public section

open Finset

namespace OddBarker

/-- Cancelling a sign: `E * S = E` with `E * E = 1` gives `S = 1`. -/
theorem fo_cancel (E S : ℤ) (hE : E * E = 1) (h : E * S = E) : S = 1 := by
  linear_combination E * h + (1 - S) * hE

/-- `∏_{k < j} (-1)^k` read off `j mod 4`. -/
theorem fo_prod_neg_one_pow (j : ℕ) :
    ∏ k ∈ range j, (-1 : ℤ) ^ k = if j % 4 = 0 ∨ j % 4 = 1 then 1 else -1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow]
      obtain ⟨r, hr⟩ := he
      split_ifs <;> omega
    · rw [ho.neg_one_pow]
      obtain ⟨r, hr⟩ := ho
      split_ifs <;> omega

/-- The folded identity on `ℕ`: `T0 (seq h) w = 1` for even `w ≤ n - 3`. -/
theorem fold_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {w : ℕ} (hw : Even w)
    (hwn : w + 3 ≤ n) : T0 (seq h) w = 1 := by
  have hN : aperiodic h (n - 1 - w) = (-1) ^ ((n - 1) / 2) := by
    apply even_shift_eq hb hn
    · obtain ⟨r, hr⟩ := hn
      obtain ⟨s, hs⟩ := hw
      exact ⟨r - s, by omega⟩
    · omega
    · omega
  rw [aperiodic_eq_sum, show n - (n - 1 - w) = w + 1 by omega] at hN
  have hterm : ∀ j ∈ range (w + 1), seq h j * seq h (j + (n - 1 - w))
      = (-1) ^ ((n - 1) / 2) * ((-1) ^ j * seq h j * seq h (w - j)) := by
    intro j hj
    have hj' : j ≤ w := by have := Finset.mem_range.mp hj; omega
    have hk : w - j < n := by omega
    have hsk := skew_seq hb hn hk
    rw [show n - 1 - (w - j) = j + (n - 1 - w) by omega] at hsk
    have hpow : (-1 : ℤ) ^ ((n - 1) / 2 + (w - j)) = (-1) ^ ((n - 1) / 2) * (-1) ^ j := by
      rw [pow_add, neg_one_pow_sub hj', hw.neg_one_pow, one_mul]
    rw [hpow] at hsk
    have hsq := seq_mul_self hb.1 hk
    linear_combination (seq h j * seq h (w - j)) * hsk - (seq h j * seq h (j + (n - 1 - w))) * hsq
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hN
  unfold T0
  exact fo_cancel _ _ (by rw [← mul_pow]; norm_num) hN

/-- The Challenge's `fold`. -/
theorem fold_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (w : ℕ) (hw : Even w)
    (hwn : w + 3 ≤ n) :
    ∑ k : Fin (w + 1), (-1) ^ k.val * h ⟨k.val, by omega⟩ * h ⟨w - k.val, by omega⟩ = 1 := by
  have hT := fold_seq hb hn hw hwn
  unfold T0 at hT
  rw [← Fin.sum_univ_eq_sum_range (fun k => (-1 : ℤ) ^ k * seq h k * seq h (w - k)) (w + 1)] at hT
  refine Eq.trans ?_ hT
  apply Finset.sum_congr rfl
  intro k _
  have hk1 : k.val < n := by omega
  have hk2 : w - k.val < n := by omega
  simp only [seq_eq h hk1, seq_eq h hk2]

/-- `∏_{i ≤ 2j} a i = a j` for `2j ≤ n - 3`. -/
theorem prod_prefix {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {j : ℕ}
    (hj : 2 * j + 3 ≤ n) :
    ∏ i ∈ range (2 * j + 1), seq h i = seq h j := by
  have hT := fold_seq hb hn (w := 2 * j) ⟨j, by ring⟩ hj
  unfold T0 at hT
  have hsplit : ∑ k ∈ range (2 * j + 1), (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)
      = 2 * ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) + (-1) ^ j := by
    rw [show 2 * j + 1 = (j + 1) + j by omega, Finset.sum_range_add, Finset.sum_range_succ]
    have hmid : (-1 : ℤ) ^ j * seq h j * seq h (2 * j - j) = (-1) ^ j := by
      rw [show 2 * j - j = j by omega, mul_assoc, seq_mul_self hb.1 (by omega), mul_one]
    have hup : ∑ x ∈ range j, (-1 : ℤ) ^ (j + 1 + x) * seq h (j + 1 + x) * seq h (2 * j - (j + 1 + x))
        = ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) := by
      rw [← Finset.sum_range_reflect (fun k => (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)) j]
      apply Finset.sum_congr rfl
      intro x hx
      have hx' : x < j := Finset.mem_range.mp hx
      show (-1 : ℤ) ^ (j + 1 + x) * seq h (j + 1 + x) * seq h (2 * j - (j + 1 + x))
        = (-1 : ℤ) ^ (j - 1 - x) * seq h (j - 1 - x) * seq h (2 * j - (j - 1 - x))
      have hp : (-1 : ℤ) ^ (j + 1 + x) = (-1) ^ (j - 1 - x) := by
        rw [show j + 1 + x = (j - 1 - x) + 2 * (x + 1) by omega, pow_add,
          (even_two_mul (x + 1)).neg_one_pow, mul_one]
      rw [hp, show 2 * j - (j + 1 + x) = j - 1 - x by omega,
        show 2 * j - (j - 1 - x) = j + 1 + x by omega]
      ring
    rw [hmid, hup]
    ring
  have hL : 2 * ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) = 1 - (-1) ^ j := by
    rw [hsplit] at hT
    linarith
  obtain ⟨hps, -⟩ := prod_signs (range j) (fun k => (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)) (by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases neg_one_pow_eq_or ℤ k with h1 | h1 <;>
    rcases seq_sign hb.1 (show k < n by omega) with h2 | h2 <;>
    rcases seq_sign hb.1 (show 2 * j - k < n by omega) with h3 | h3 <;>
    simp only [h1, h2, h3] <;> norm_num)
  simp only [Finset.card_range] at hps
  have hE := fo_prod_neg_one_pow j
  have hPE : ∏ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)
      = ∏ k ∈ range j, (-1 : ℤ) ^ k := by
    rw [hps, hE]
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow] at hL
      obtain ⟨r, hr⟩ := he
      split_ifs <;> omega
    · rw [ho.neg_one_pow] at hL
      obtain ⟨r, hr⟩ := ho
      split_ifs <;> omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc] at hPE
  have hAB := fo_cancel _ _ (by rw [hE]; split_ifs <;> norm_num) hPE
  have hrefl : ∏ x ∈ range j, seq h (j + 1 + x) = ∏ k ∈ range j, seq h (2 * j - k) := by
    rw [← Finset.prod_range_reflect (fun x => seq h (j + 1 + x)) j]
    apply Finset.prod_congr rfl
    intro x hx
    have hx' : x < j := Finset.mem_range.mp hx
    show seq h (j + 1 + (j - 1 - x)) = seq h (2 * j - x)
    rw [show j + 1 + (j - 1 - x) = 2 * j - x by omega]
  rw [show 2 * j + 1 = (j + 1) + j by omega, Finset.prod_range_add, Finset.prod_range_succ, hrefl]
  linear_combination seq h j * hAB

/-- The doubling law on `ℕ`: `a (u - 1) a u = a (2u - 1) a (2u)` for `1 ≤ u`, `2u + 3 ≤ n`. -/
theorem doubling_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {u : ℕ} (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) :
    seq h (u - 1) * seq h u = seq h (2 * u - 1) * seq h (2 * u) := by
  have h1 := prod_prefix hb hn (j := u) hun
  have h2 := prod_prefix hb hn (j := u - 1) (by omega)
  rw [show 2 * u + 1 = (2 * (u - 1) + 1) + 1 + 1 by omega, Finset.prod_range_succ,
    Finset.prod_range_succ, h2, show 2 * (u - 1) + 1 + 1 = 2 * u by omega,
    show 2 * (u - 1) + 1 = 2 * u - 1 by omega] at h1
  have hsq := seq_mul_self hb.1 (show u - 1 < n by omega)
  linear_combination (-seq h (u - 1)) * h1 + (seq h (2 * u - 1) * seq h (2 * u)) * hsq

/-- The Challenge's `doubling`. -/
theorem doubling_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (u : ℕ)
    (hu : 1 ≤ u) (hun : 2 * u + 3 ≤ n) :
    h ⟨u - 1, by omega⟩ * h ⟨u, by omega⟩ = h ⟨2 * u - 1, by omega⟩ * h ⟨2 * u, by omega⟩ := by
  have hd := doubling_seq hb hn hu hun
  rwa [seq_eq h (show u - 1 < n by omega), seq_eq h (show u < n by omega),
    seq_eq h (show 2 * u - 1 < n by omega), seq_eq h (show 2 * u < n by omega)] at hd

end OddBarker
