module

public import OB.Parity
public import OB.Compose

/-!
# The even reduction (Turyn–Storer, footnote 2) and the circulant Hadamard composition

For even `n > 2` and a Barker sequence: even shifts vanish (`even_shift_zero_of_even`), so the
mod-four congruence at `u = 2` (`aperiodic_add_aperiodic_sub_mod_four`) gives `4 ∣ n`
(`four_dvd_of_even_internal`); then every periodic autocorrelation
`periodic h a = ∑ j, h j * h (j - a) = C(a) + C(n - a)` (`periodic_eq_aperiodic_add`, `a ≠ 0`) lies in
`[-2, 2]` and is `≡ n ≡ 0 (mod 4)`, so it is `0` (`periodic_offpeak_zero`); the circulant matrix
`circ h i j = h (j - i)` then has `H Hᵀ = n I` entrywise (`(H Hᵀ) i j = periodic h (j - i)`), is a sign
matrix, and is circulant by definition (`existsRealCirculantHadamard_of_even_internal`). Composing
with the circulant Hadamard statement of `openai/math` (`exists_iff_order_one_or_four`, taken as the
hypothesis `hcirc` in its `→` direction) gives the even half, hence the full classification.

The route follows `lean/OAI/LinearAlgebra/Barker/{Parity,Wraparound,PeriodicModFour,Main}.lean` of
`openai/math` in outline (Apache-2.0; see NOTICE); the proofs here are written for this repository.

Lane: **hadamard**.
-/

@[expose] public section

open Finset

namespace OddBarker

/-- The Challenge's `four_dvd_of_even`. -/
theorem four_dvd_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n)
    (hb : IsBarker h) : 4 ∣ n := by
  sorry

/-- The periodic autocorrelation at shift `a` (the definition of `openai/math`'s `Barker/Model.lean`,
adapted). -/
def periodic {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, h j * h (j - a)

theorem periodic_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) :
    periodic h 0 = n := by
  sorry

/-- `periodic h a = C(a) + C(n - a)` for `a ≠ 0`. -/
theorem periodic_eq_aperiodic_add {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) (ha : a ≠ 0) :
    periodic h a = aperiodic h a.val + aperiodic h (n - a.val) := by
  sorry

theorem periodic_offpeak_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n)
    (h2 : 2 < n) (a : Fin n) (ha : a ≠ 0) : periodic h a = 0 := by
  sorry

/-- The circulant matrix of `h`: `circ h i j = h (j - i)`. -/
def circ {n : ℕ} (h : Fin n → ℤ) : RealMatrix n := fun i j => (h (j - i) : ℝ)

theorem circ_isCirculant {n : ℕ} (h : Fin n → ℤ) : IsCirculant (circ h) := by
  sorry

theorem circ_isSignHadamard {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) (h2 : 2 < n) :
    IsSignHadamard (circ h) := by
  sorry

/-- The Challenge's `existsRealCirculantHadamard_of_even`. -/
theorem existsRealCirculantHadamard_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n)
    (h2 : 2 < n) (hb : IsBarker h) : ExistsRealCirculantHadamard n := by
  sorry

/-- The even half from the circulant Hadamard statement. -/
theorem even_length_eq_two_or_four_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  sorry

/-- The Challenge's `exists_iff_of_circulantHadamard`. -/
theorem exists_iff_of_circulantHadamard_internal
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- The Challenge's `length_le_thirteen_of_circulantHadamard`. -/
theorem length_le_thirteen_of_circulantHadamard_internal
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  sorry

end OddBarker
