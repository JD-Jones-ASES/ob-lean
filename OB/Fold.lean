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

/-- The folded identity on `ℕ`: `T0 (seq h) w = 1` for even `w ≤ n - 3`. -/
theorem fold_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {w : ℕ} (hw : Even w)
    (hwn : w + 3 ≤ n) : T0 (seq h) w = 1 := by
  sorry

/-- The Challenge's `fold`. -/
theorem fold_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (w : ℕ) (hw : Even w)
    (hwn : w + 3 ≤ n) :
    ∑ k : Fin (w + 1), (-1) ^ k.val * h ⟨k.val, by omega⟩ * h ⟨w - k.val, by omega⟩ = 1 := by
  sorry

/-- `∏_{i ≤ 2j} a i = a j` for `2j ≤ n - 3`. -/
theorem prod_prefix {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {j : ℕ}
    (hj : 2 * j + 3 ≤ n) :
    ∏ i ∈ range (2 * j + 1), seq h i = seq h j := by
  sorry

/-- The doubling law on `ℕ`: `a (u - 1) a u = a (2u - 1) a (2u)` for `1 ≤ u`, `2u + 3 ≤ n`. -/
theorem doubling_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {u : ℕ} (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) :
    seq h (u - 1) * seq h u = seq h (2 * u - 1) * seq h (2 * u) := by
  sorry

/-- The Challenge's `doubling`. -/
theorem doubling_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (u : ℕ)
    (hu : 1 ≤ u) (hun : 2 * u + 3 ≤ n) :
    h ⟨u - 1, by omega⟩ * h ⟨u, by omega⟩ = h ⟨2 * u - 1, by omega⟩ * h ⟨2 * u, by omega⟩ := by
  sorry

end OddBarker
