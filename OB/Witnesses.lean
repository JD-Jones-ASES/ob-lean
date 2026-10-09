module

public import OB.Defs

/-!
# The Barker sequences of lengths 1, 2, 3, 4, 5, 7, 11, 13

The sequences of Schmidt–Willms's introduction (normalised to begin `+ +`), each checked by
`decide` shift by shift. 
-/

@[expose] public section

namespace OddBarker

def a1 : Fin 1 → ℤ := ![1]
def a2 : Fin 2 → ℤ := ![1, 1]
def a3 : Fin 3 → ℤ := ![1, 1, -1]
def a4 : Fin 4 → ℤ := ![1, 1, 1, -1]
def a5 : Fin 5 → ℤ := ![1, 1, 1, -1, 1]
def a7 : Fin 7 → ℤ := ![1, 1, 1, -1, -1, 1, -1]
def a11 : Fin 11 → ℤ := ![1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1]
def a13 : Fin 13 → ℤ := ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1]

theorem a1_isBarker : IsBarker a1 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a1 j = 1 ∨ a1 j = -1
    decide
  · intro k hk0 hkn
    omega

theorem a2_isBarker : IsBarker a2 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a2 j = 1 ∨ a2 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k
    decide

theorem a3_isBarker : IsBarker a3 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a3 j = 1 ∨ a3 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

theorem a4_isBarker : IsBarker a4 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a4 j = 1 ∨ a4 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

theorem a5_isBarker : IsBarker a5 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a5 j = 1 ∨ a5 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

theorem a7_isBarker : IsBarker a7 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a7 j = 1 ∨ a7 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

theorem a11_isBarker : IsBarker a11 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a11 j = 1 ∨ a11 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

theorem a13_isBarker : IsBarker a13 := by
  refine ⟨?_, ?_⟩
  · show ∀ j, a13 j = 1 ∨ a13 j = -1
    decide
  · intro k hk0 hkn
    interval_cases k <;> decide

/-- `+++++--++-+--` (the last sign of `a13` flipped) has `C(1) = 2`: a forged witness is rejected. -/
def forged13 : Fin 13 → ℤ := ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1]

theorem forged13_not_isBarker : ¬ IsBarker forged13 := by
  intro hb
  have h1 := hb.2 1 (by decide) (by decide)
  revert h1
  decide

/-! Sanity values of the shift-one autocorrelation `C(1)` (computed by hand from the sequences). -/

theorem wi_a2_aperiodic_one : aperiodic a2 1 = 1 := by decide
theorem wi_a3_aperiodic_one : aperiodic a3 1 = 0 := by decide
theorem wi_a4_aperiodic_one : aperiodic a4 1 = 1 := by decide
theorem wi_a5_aperiodic_one : aperiodic a5 1 = 0 := by decide
theorem wi_a7_aperiodic_one : aperiodic a7 1 = 0 := by decide
theorem wi_a11_aperiodic_one : aperiodic a11 1 = 0 := by decide
theorem wi_a13_aperiodic_one : aperiodic a13 1 = 0 := by decide
theorem wi_forged13_aperiodic_one : aperiodic forged13 1 = 2 := by decide

end OddBarker
