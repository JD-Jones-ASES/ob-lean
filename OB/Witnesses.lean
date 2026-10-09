module

public import OB.Defs

/-!
# The Barker sequences of lengths 1, 2, 3, 4, 5, 7, 11, 13

The sequences of Schmidt–Willms's introduction (normalised to begin `+ +`), each checked by
`decide` shift by shift. The length-13 witness and its forged control were checked at the bench on
2026-10-06 (lane K2).

Lane: **witnesses**.
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

theorem a1_isBarker : IsBarker a1 := by sorry
theorem a2_isBarker : IsBarker a2 := by sorry
theorem a3_isBarker : IsBarker a3 := by sorry
theorem a4_isBarker : IsBarker a4 := by sorry
theorem a5_isBarker : IsBarker a5 := by sorry
theorem a7_isBarker : IsBarker a7 := by sorry
theorem a11_isBarker : IsBarker a11 := by sorry
theorem a13_isBarker : IsBarker a13 := by sorry

/-- `+++++--++-+--` (the last sign of `a13` flipped) has `C(1) = 2`: a forged witness is rejected. -/
def forged13 : Fin 13 → ℤ := ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1]

theorem forged13_not_isBarker : ¬ IsBarker forged13 := by sorry

end OddBarker
