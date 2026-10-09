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

/-! ## The enumeration (lane helpers, prefix `un_`) -/

/-- The aperiodic autocorrelation of a list at shift `k`. -/
def un_ac (L : List ℤ) (k : ℕ) : ℤ := (List.zipWith (· * ·) L (L.drop k)).sum

/-- The Barker test on a list: `|C(k)| ≤ 1` for every `0 < k < length`. -/
def un_bark (L : List ℤ) : Bool :=
  (List.range L.length).all fun k => k == 0 || decide (-1 ≤ un_ac L k ∧ un_ac L k ≤ 1)

/-- Every `±1` list of length `n`. -/
def un_all : ℕ → List (List ℤ)
  | 0 => [[]]
  | n + 1 => (un_all n).flatMap fun l => [1 :: l, -1 :: l]

/-- The four listed sequences of length `n`: `±canon n`, `±alt (canon n)`. -/
def un_ans (n : ℕ) : List (List ℤ) :=
  [List.ofFn (fun j : Fin n => (1 : ℤ) * canon n j),
   List.ofFn (fun j : Fin n => (-1 : ℤ) * canon n j),
   List.ofFn (fun j : Fin n => (1 : ℤ) * (-1) ^ j.val * canon n j),
   List.ofFn (fun j : Fin n => (-1 : ℤ) * (-1) ^ j.val * canon n j)]

/-- A list passes if it is not Barker or is one of the four listed sequences. -/
def un_good (n : ℕ) (L : List ℤ) : Bool := !un_bark L || decide (L ∈ un_ans n)

theorem un_mem_all : ∀ l : List ℤ, (∀ x ∈ l, x = 1 ∨ x = -1) → l ∈ un_all l.length
  | [], _ => by simp [un_all]
  | x :: l, hx => by
    have ih := un_mem_all l (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    simp only [List.length_cons, un_all, List.mem_flatMap]
    refine ⟨l, ih, ?_⟩
    rcases hx x List.mem_cons_self with rfl | rfl <;> simp

theorem un_ac_ofFn {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    un_ac (List.ofFn h) k = aperiodic h k := by
  unfold un_ac aperiodic
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zipWith, List.getElem_drop, List.getElem_ofFn]
    congr 2 <;> (try simp only [Fin.ext_iff, Fin.val_mk]) <;> omega

theorem un_bark_of {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) : un_bark (List.ofFn h) = true := by
  unfold un_bark
  rw [List.all_eq_true]
  intro k hk
  rw [List.length_ofFn, List.mem_range] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have := abs_le.mp (hb.2 k hk0 hk)
    rw [un_ac_ofFn]
    simp [this]

/-- The uniqueness conclusion at any length `n` whose enumeration check passes. -/
theorem un_of_check {n : ℕ} (hc : (un_all n).all (un_good n) = true) (h : Fin n → ℤ)
    (hb : IsBarker h) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((∀ j, h j = ε * canon n j) ∨ (∀ j, h j = ε * (-1) ^ j.val * canon n j)) := by
  have hmem : List.ofFn h ∈ un_all n := by
    have := un_mem_all (List.ofFn h) (by
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' h x).mp hx
      exact hb.1 i)
    simpa using this
  have hg := List.all_eq_true.mp hc _ hmem
  simp only [un_good, un_bark_of hb, Bool.not_true, Bool.false_or, decide_eq_true_eq, un_ans,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | hg | hg | hg <;> have hf := List.ofFn_injective hg
  · exact ⟨1, Or.inl rfl, Or.inl fun j => congrFun hf j⟩
  · exact ⟨-1, Or.inr rfl, Or.inl fun j => congrFun hf j⟩
  · exact ⟨1, Or.inl rfl, Or.inr fun j => congrFun hf j⟩
  · exact ⟨-1, Or.inr rfl, Or.inr fun j => congrFun hf j⟩

theorem un_check1 : (un_all 1).all (un_good 1) = true := by decide +kernel
theorem un_check3 : (un_all 3).all (un_good 3) = true := by decide +kernel
theorem un_check5 : (un_all 5).all (un_good 5) = true := by decide +kernel
theorem un_check7 : (un_all 7).all (un_good 7) = true := by decide +kernel
theorem un_check11 : (un_all 11).all (un_good 11) = true := by decide +kernel
theorem un_check13 : (un_all 13).all (un_good 13) = true := by decide +kernel

theorem unique_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((∀ j, h j = ε * canon n j) ∨ (∀ j, h j = ε * (-1) ^ j.val * canon n j)) := by
  rcases odd_length_mem_internal h hn hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact un_of_check un_check1 h hb
  · exact un_of_check un_check3 h hb
  · exact un_of_check un_check5 h hb
  · exact un_of_check un_check7 h hb
  · exact un_of_check un_check11 h hb
  · exact un_of_check un_check13 h hb

end OddBarker
