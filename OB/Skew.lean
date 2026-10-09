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
  sorry

/-- Skew-symmetry on `ℕ`: for odd `n`, a Barker sequence and `k < n`,
`a k * a (n - 1 - k) = (-1)^((n - 1)/2 + k)`. -/
theorem skew_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ} (hk : k < n) :
    seq h k * seq h (n - 1 - k) = (-1) ^ ((n - 1) / 2 + k) := by
  sorry

/-- The Challenge's `skew`. -/
theorem skew_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : Fin n) :
    h k * h (Fin.rev k) = (-1) ^ ((n - 1) / 2 + k.val) := by
  sorry

/-- Sign changes mirror with a flip: for `1 ≤ s ≤ n - 1`,
`a (s - 1) * a s = -(a (n - s - 1) * a (n - s))`. -/
theorem skew_pair {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s + 1 ≤ n) :
    seq h (s - 1) * seq h s = -(seq h (n - s - 1) * seq h (n - s)) := by
  sorry

end OddBarker
