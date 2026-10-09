module

public import Mathlib

/-!
# Barker sequences of odd length

A Barker sequence of length `n` is a `±1` sequence `h : Fin n → ℤ` whose aperiodic autocorrelations
`C(k) = ∑_{j < n - k} h j * h (j + k)`, `0 < k < n`, all have absolute value at most one. Turyn and
Storer (*On binary sequences*, Proc. Amer. Math. Soc. 12 (1961) 394–399) proved that a Barker
sequence of odd length has length at most 13, and that the odd lengths that occur are 1, 3, 5, 7, 11
and 13; their Theorem 1(iv), used by that proof, is false as stated (Willms, arXiv:1404.4833), and
the proof formalized here is that of Schmidt and Willms (*Barker sequences of odd length*, Des.
Codes Cryptogr. 80 (2016) 409–414, arXiv:1501.06035), recast so that no enumeration of sequences is needed.
This file states, and `Solution.lean` proves:

* the classification: a Barker sequence of odd length `n` exists exactly when
  `n ∈ {1, 3, 5, 7, 11, 13}` (`odd_length_mem`, `odd_exists_iff`), and such a sequence is the listed one
  of its length up to negation and alternation (`unique`, by a kernel enumeration);
* the structure of a Barker sequence of odd length `n`: odd shifts have autocorrelation `0` and even
  shifts `(-1)^((n-1)/2)` (`aperiodic_eq`); skew-symmetry `h k * h (n - 1 - k) = (-1)^((n-1)/2 + k)`
  (`skew`); the folded identity `∑_{k ≤ w} (-1)^k h k h (w - k) = 1` for even `w ≤ n - 3` (`fold`);
  the doubling law `h (u-1) h u = h (2u-1) h (2u)` for `1 ≤ u ≤ (n-3)/2` (`doubling`); and the run
  bounds of Schmidt and Willms (Lemmas 3 and 4): for `n ≥ 7` and `h 0 = h 1`, with `p` the first
  position where the sign changes and `q` the first such position not divisible by `p`, both are odd
  and `2q - 3 ≤ n ≤ p + q + 1` (`run_bounds`);
* the even half as hypotheses, so that the full classification composes: if every Barker sequence of
  positive even length has length 2 or 4 (the statement `even_length_eq_two_or_four` of `openai/math`,
  family 179), then a Barker sequence of positive length `n` exists exactly when
  `n ∈ {1, 2, 3, 4, 5, 7, 11, 13}`, and every Barker sequence has length at most 13
  (`exists_iff_of_even`, `length_le_thirteen_of_even`);
* the even reduction of Turyn and Storer: an even-length Barker sequence of length `n > 2` has
  `4 ∣ n` and yields a real circulant Hadamard matrix of order `n` (`four_dvd_of_even`,
  `existsRealCirculantHadamard_of_even`); hence, if real circulant Hadamard matrices of positive
  order exist only at orders 1 and 4 (the statement `exists_iff_order_one_or_four` of `openai/math`),
  the same two conclusions follow (`exists_iff_of_circulantHadamard`,
  `length_le_thirteen_of_circulantHadamard`).

`IsSign`, `aperiodic` and `IsBarker` repeat `lean/ComparatorChallenges/EvenBarker.lean` of
`openai/math` character for character, and `RealMatrix`, `IsCirculant`, `IsSignHadamard` and
`ExistsRealCirculantHadamard` repeat `lean/ComparatorChallenges/CirculantHadamard.lean` (commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0; see NOTICE), so that the two theorems of that
project discharge the hypotheses of the conditional theorems below by unfolding alone.

This Mathlib-only file intentionally contains placeholders; the corresponding Solution declarations
are proved in a separate environment.
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

/-! ### The classification of odd lengths -/

/-- A Barker sequence of odd length has length 1, 3, 5, 7, 11 or 13 (Turyn–Storer 1961, Theorem 2
with the list of the introduction; the proof of Schmidt–Willms 2016). -/
theorem odd_length_mem {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- For odd `n`, a Barker sequence of length `n` exists exactly when `n ∈ {1, 3, 5, 7, 11, 13}`. -/
theorem odd_exists_iff {n : ℕ} (hn : Odd n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔ n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- Uniqueness: a Barker sequence of odd length is the listed one of its length up to negation and
alternation, `h = ε • canon n` or `h = ε • ((-1)^j • canon n)` with `ε = ±1`. -/
theorem unique {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((∀ j, h j = ε * canon n j) ∨ (∀ j, h j = ε * (-1) ^ j.val * canon n j)) := by
  sorry

/-! ### The structure of a Barker sequence of odd length -/

/-- For odd `n`, odd shifts have autocorrelation `0` and even shifts `(-1)^((n-1)/2)`
(Turyn–Storer; the first step of Schmidt–Willms, Lemma 2). -/
theorem aperiodic_eq {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 := by
  sorry

/-- Skew-symmetry (Schmidt–Willms, Lemma 2(i)): for odd `n`,
`h k * h (n - 1 - k) = (-1)^((n - 1)/2 + k)`. -/
theorem skew {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : Fin n) :
    h k * h (Fin.rev k) = (-1) ^ ((n - 1) / 2 + k.val) := by
  sorry

/-- The folded identity: for odd `n` and even `w ≤ n - 3`, `∑_{k ≤ w} (-1)^k h k h (w - k) = 1`
(the even-shift autocorrelation at shift `n - 1 - w`, rewritten through skew-symmetry). -/
theorem fold {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (w : ℕ) (hw : Even w)
    (hwn : w + 3 ≤ n) :
    ∑ k : Fin (w + 1), (-1) ^ k.val * h ⟨k.val, by omega⟩ * h ⟨w - k.val, by omega⟩ = 1 := by
  sorry

/-- The doubling law (Schmidt–Willms, Lemma 2(ii)): for odd `n` and `1 ≤ u ≤ (n - 3)/2`,
`h (u - 1) * h u = h (2u - 1) * h (2u)`. -/
theorem doubling {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (u : ℕ) (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) :
    h ⟨u - 1, by omega⟩ * h ⟨u, by omega⟩ = h ⟨2 * u - 1, by omega⟩ * h ⟨2 * u, by omega⟩ := by
  sorry

/-- The run bounds (Schmidt–Willms, Lemmas 3 and 4). For odd `n ≥ 7` and a Barker sequence with
`h 0 = h 1`, let `p` be the least position `s ≥ 1` with `h s ≠ h (s - 1)` (the length of the first
run) and `q` the least such position not divisible by `p` (the sum of the lengths of the first runs
up to the first one whose length `p` does not divide). Then `p` and `q` are odd, `2q - 3 ≤ n` and
`n ≤ p + q + 1`. -/
theorem run_bounds {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (h7 : 7 ≤ n)
    (h01 : h ⟨0, by omega⟩ = h ⟨1, by omega⟩) (p q : ℕ)
    (hpn : p < n) (hpB : h ⟨p, hpn⟩ ≠ h ⟨p - 1, by omega⟩)
    (hpmin : ∀ s (hs0 : 0 < s) (hsp : s < p), h ⟨s, by omega⟩ = h ⟨s - 1, by omega⟩)
    (hqn : q < n) (hqB : h ⟨q, hqn⟩ ≠ h ⟨q - 1, by omega⟩) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s (hs0 : 0 < s) (hsq : s < q), h ⟨s, by omega⟩ ≠ h ⟨s - 1, by omega⟩ → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  sorry

/-! ### The even reduction (Turyn–Storer, footnote 2) -/

/-- A Barker sequence of even length `n > 2` has `4 ∣ n`. -/
theorem four_dvd_of_even {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n) (hb : IsBarker h) :
    4 ∣ n := by
  sorry

/-- A Barker sequence of even length `n > 2` yields a real circulant Hadamard matrix of order `n`:
its periodic autocorrelations vanish off the peak. -/
theorem existsRealCirculantHadamard_of_even {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n)
    (hb : IsBarker h) : ExistsRealCirculantHadamard n := by
  sorry

/-! ### The full classification, given the even half -/

/-- If every Barker sequence of positive even length has length 2 or 4, then a Barker sequence of
positive length `n` exists exactly when `n ∈ {1, 2, 3, 4, 5, 7, 11, 13}`. -/
theorem exists_iff_of_even
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- Under the same hypothesis, every Barker sequence has length at most 13. -/
theorem length_le_thirteen_of_even
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  sorry

/-- If real circulant Hadamard matrices of positive order exist only at orders 1 and 4, then a
Barker sequence of positive length `n` exists exactly when `n ∈ {1, 2, 3, 4, 5, 7, 11, 13}`. -/
theorem exists_iff_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  sorry

/-- Under the same hypothesis, every Barker sequence has length at most 13. -/
theorem length_le_thirteen_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  sorry

end OddBarker
