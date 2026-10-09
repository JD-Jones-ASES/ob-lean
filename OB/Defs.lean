module

public import Mathlib

/-!
# Definitions

The eight definitions of `Challenge.lean`, restated character for character (the import is the same,
`Mathlib`, so that every definition elaborates to the same term in both files; the registry's
comparator judges the elaborated constants). `scripts/check_definitions.py` compares the two files
with the two upstream files of `openai/math` they are restated from: `IsSign`, `aperiodic` and
`IsBarker` from `lean/ComparatorChallenges/EvenBarker.lean`; `RealMatrix`, `IsCirculant`,
`IsSignHadamard` and `ExistsRealCirculantHadamard` from `lean/ComparatorChallenges/CirculantHadamard.lean`
(commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0; see NOTICE).
-/

@[expose] public section

namespace OddBarker

universe u

/-- `x` is `1` or `-1`. -/
def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

open scoped BigOperators

/-- The aperiodic autocorrelation of `h` at shift `k`: `∑_{j < n - k} h j * h (j + k)`. -/
def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩

/-- Every entry is a sign and every nontrivial aperiodic autocorrelation has absolute value at
most one. -/
def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1

/-- Real `n × n` matrices. -/
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- `H` is circulant: `H i j` depends only on `j - i` in `Fin n`. -/
def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

/-- `H` is a `±1` matrix with `H Hᵀ = n I`. -/
def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

/-- A real circulant Hadamard matrix of order `n` exists. -/
def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H

/-- The listed Barker sequence of each odd length (`fun _ => 1` at other lengths): the sequences of
Schmidt–Willms's introduction, normalised to begin `+ +`. -/
def canon : (n : ℕ) → Fin n → ℤ
  | 1 => ![1]
  | 3 => ![1, 1, -1]
  | 5 => ![1, 1, 1, -1, 1]
  | 7 => ![1, 1, 1, -1, -1, 1, -1]
  | 11 => ![1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1]
  | 13 => ![1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1]
  | _ => fun _ => 1

end OddBarker
