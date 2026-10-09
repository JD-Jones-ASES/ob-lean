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

/-- `C(u) + C(n - u) ≡ n (mod 4)` for a sign sequence and `0 < u < n`. -/
theorem aperiodic_add_aperiodic_sub_mod_four {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j))
    {u : ℕ} (hu0 : 0 < u) (hun : u < n) :
    (4 : ℤ) ∣ aperiodic h u + aperiodic h (n - u) - n := by
  sorry

/-- For odd `n` and a Barker sequence, every even nontrivial shift has autocorrelation
`(-1)^((n-1)/2)`. -/
theorem even_shift_eq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = (-1) ^ ((n - 1) / 2) := by
  sorry

/-- The Challenge's `aperiodic_eq`. -/
theorem aperiodic_eq_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 := by
  sorry

/-- For even `n` and a Barker sequence, every even nontrivial shift has autocorrelation `0`
(parity: `C(k) ≡ n - k ≡ 0 (mod 2)` and `|C(k)| ≤ 1`). -/
theorem even_shift_zero_of_even {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  sorry

end OddBarker
