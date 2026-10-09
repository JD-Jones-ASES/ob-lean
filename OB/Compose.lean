module

public import OB.Endgame
public import OB.Witnesses

/-!
# The classification, and its composition with the even half

`odd_exists_iff_internal` from `odd_length_mem_internal` and the six odd witnesses;
`exists_iff_of_even_internal` and `length_le_thirteen_of_even_internal` with the even-length
statement of `openai/math` (`even_length_eq_two_or_four`) as the hypothesis `heven`, in exactly its
shape (implicit `n`), so that it is discharged by the theorem itself.

Lane: **compose**.
-/

@[expose] public section

namespace OddBarker

/-- The Challenge's `odd_exists_iff`. -/
theorem odd_exists_iff_internal {n : ℕ} (hn : Odd n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔ n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- The Challenge's `exists_iff_of_even`. -/
theorem exists_iff_of_even_internal
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- The Challenge's `length_le_thirteen_of_even`. -/
theorem length_le_thirteen_of_even_internal
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  sorry

end OddBarker
