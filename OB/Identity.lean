module

public import OB.Defs

/-!
# The folded sum and its step identity

`T0 a w = ∑_{k ≤ w} (-1)^k a k a (w - k)`. For even `w` and any `a : ℕ → ℤ`,
`T0 a (w + 2) - T0 a w = 2 a 0 Δ(w + 1) - ∑_{t ≤ w} (-1)^t Δ t Δ (w - t)` with `Δ t = a (t+1) - a t`:
the generating-function identity `(1 - x²) a(x) a(-x) = [(1 - x) a(x)] [(1 + x) a(-x)]` read off at
`x^{w+2}`. This is the identity behind Schmidt–Willms's Lemma 4. Ported from the bench probes of
2026-10-06 (lane K2).
-/

@[expose] public section

open Finset

namespace OddBarker

/-- The folded sum `∑_{k ≤ w} (-1)^k a k a (w - k)`. -/
def T0 (a : ℕ → ℤ) (w : ℕ) : ℤ :=
  ∑ k ∈ range (w + 1), (-1) ^ k * a k * a (w - k)

theorem neg_one_pow_sub {N k : ℕ} (hk : k ≤ N) :
    (-1 : ℤ) ^ (N - k) = (-1) ^ N * (-1) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add]
  have h : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  linear_combination (-(-1 : ℤ) ^ d) * h

/-- At odd arguments the folded sum vanishes identically. -/
theorem T0_odd (a : ℕ → ℤ) {w : ℕ} (hw : Even w) : T0 a (w + 1) = 0 := by
  unfold T0
  have h := Finset.sum_range_reflect (fun k => (-1 : ℤ) ^ k * a k * a (w + 1 - k)) (w + 2)
  have hneg : ∑ j ∈ range (w + 2), (fun k => (-1 : ℤ) ^ k * a k * a (w + 1 - k)) (w + 2 - 1 - j)
      = -∑ j ∈ range (w + 2), (-1 : ℤ) ^ j * a j * a (w + 1 - j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ w + 1 := by simp at hj; omega
    have e1 : w + 2 - 1 - j = w + 1 - j := by omega
    have e2 : w + 1 - (w + 1 - j) = j := by omega
    simp only [e1, e2]
    rw [neg_one_pow_sub hj', pow_succ, hw.neg_one_pow]
    ring
  linarith [h, hneg]

/-- The step identity. -/
theorem T0_step (a : ℕ → ℤ) {w : ℕ} (hw : Even w) :
    T0 a (w + 2) - T0 a w = 2 * a 0 * (a (w + 2) - a (w + 1)) -
      ∑ t ∈ range (w + 1), (-1) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t)) := by
  set S1 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a (t + 1) * a (w - t + 1) with hS1
  set S2 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a (t + 1) * a (w - t) with hS2
  set S3 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a t * a (w - t + 1) with hS3
  have hsplit : ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t))
      = S1 - S2 - S3 + T0 a w := by
    unfold T0
    rw [hS1, hS2, hS3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have h1 : T0 a (w + 2) = -S1 + 2 * a 0 * a (w + 2) := by
    unfold T0
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hS1, ← Finset.sum_neg_distrib]
    have hmid : ∑ i ∈ range (w + 1), (-1 : ℤ) ^ (i + 1) * a (i + 1) * a (w + 2 - (i + 1))
        = ∑ i ∈ range (w + 1), -((-1 : ℤ) ^ i * a (i + 1) * a (w - i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ w := by simp at hi; omega
      have e : w + 2 - (i + 1) = w - i + 1 := by omega
      rw [e, pow_succ]
      ring
    rw [hmid]
    have e2 : w + 2 - (w + 1 + 1) = 0 := by omega
    rw [e2, Nat.sub_zero, pow_succ, pow_succ, hw.neg_one_pow]
    ring
  have h2 : S2 = a 0 * a (w + 1) := by
    have h := T0_odd a hw
    unfold T0 at h
    rw [Finset.sum_range_succ'] at h
    have hmid : ∑ i ∈ range (w + 1), (-1 : ℤ) ^ (i + 1) * a (i + 1) * a (w + 1 - (i + 1))
        = -S2 := by
      rw [hS2, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have e : w + 1 - (i + 1) = w - i := by omega
      rw [e, pow_succ]
      ring
    rw [hmid] at h
    simp at h
    linarith
  have h3 : S3 = S2 := by
    rw [hS3, hS2, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ w := by simp at hj; omega
    have e1 : w + 1 - 1 - j = w - j := by omega
    have e2 : w - (w - j) + 1 = j + 1 := by omega
    rw [e1, e2, neg_one_pow_sub hj', hw.neg_one_pow]
    ring
  rw [hsplit, h1, h3, h2]
  ring

end OddBarker
