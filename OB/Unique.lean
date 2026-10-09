module

public import OB.Compose

/-!
# Uniqueness (stretch): every Barker sequence of odd length is the listed one up to negation and
alternation

Schmidt–Willms's introduction: `h ↦ (-1)^(a + b j) h j` preserves the Barker property, and the only
Barker sequences beginning `+ +` of odd length are `a3, a5, a7, a11, a13` (and `a1 = [1]`). In Lean:
for odd `n` and a Barker `h`, some `ε ∈ {1, -1}` has `h = ε • canon n` or `h = ε • alt (canon n)`.
Route: `odd_length_mem_internal` fixes `n`; skew-symmetry (`skew_internal`) determines `h` from its
first `(n + 1)/2` values; the remaining `2^((n+1)/2)` sign patterns (`128` at `n = 13`) are checked
by the kernel (a `Nat`-coded enumeration, `decide +kernel`, never `native_decide`), or any smaller
route the lane finds. Kill: 2.5 h of lane time, or a kernel check above 10 minutes.

Lane: **unique** (stretch).
-/

@[expose] public section

namespace OddBarker

/-- The listed Barker sequence of each odd length (`fun _ => 1` elsewhere). -/
def canon : (n : ℕ) → Fin n → ℤ
  | 1 => ![1]
  | 3 => ![1, 1, -1]
  | 5 => ![1, 1, 1, -1, 1]
  | 7 => ![1, 1, 1, -1, -1, 1, -1]
  | 11 => ![1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1]
  | 13 => ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1]
  | _ => fun _ => 1

theorem unique_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((∀ j, h j = ε * canon n j) ∨ (∀ j, h j = ε * (-1) ^ j.val * canon n j)) := by
  sorry

end OddBarker
