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
  constructor
  · rintro ⟨h, hb⟩
    exact odd_length_mem_internal h hn hb
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨a1, a1_isBarker⟩
    · exact ⟨a3, a3_isBarker⟩
    · exact ⟨a5, a5_isBarker⟩
    · exact ⟨a7, a7_isBarker⟩
    · exact ⟨a11, a11_isBarker⟩
    · exact ⟨a13, a13_isBarker⟩

/-- The Challenge's `exists_iff_of_even`. -/
theorem exists_iff_of_even_internal
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  constructor
  · rintro ⟨h, hb⟩
    rcases Nat.even_or_odd n with he | ho
    · rcases heven h hn he hb with rfl | rfl <;> decide
    · rcases odd_length_mem_internal h ho hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨a1, a1_isBarker⟩
    · exact ⟨a2, a2_isBarker⟩
    · exact ⟨a3, a3_isBarker⟩
    · exact ⟨a4, a4_isBarker⟩
    · exact ⟨a5, a5_isBarker⟩
    · exact ⟨a7, a7_isBarker⟩
    · exact ⟨a11, a11_isBarker⟩
    · exact ⟨a13, a13_isBarker⟩

/-- The Challenge's `length_le_thirteen_of_even`. -/
theorem length_le_thirteen_of_even_internal
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · rcases (exists_iff_of_even_internal heven hn).1 ⟨h, hb⟩ with
      e | e | e | e | e | e | e | e <;> omega

/-- Odd lengths: a Barker sequence of odd length `n` has `n ≤ 13`. -/
theorem co_length_le_thirteen_of_odd {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n ≤ 13 := by
  rcases odd_length_mem_internal h hn hb with e | e | e | e | e | e <;> omega

/-- Odd lengths: no Barker sequence of odd length `n > 13`. -/
theorem co_not_isBarker_of_odd_gt {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (h13 : 13 < n) :
    ¬ IsBarker h := fun hb => by
  have := co_length_le_thirteen_of_odd h hn hb
  omega


end OddBarker
