module

public import OB

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (`OB/Endgame.lean`, `Compose.lean`, `Parity.lean`, `Skew.lean`,
`Fold.lean`, `Runs.lean`, `Hadamard.lean`). This module does not import `Challenge.lean`; the
definitions come from `OB/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace OddBarker

/-! ### The classification of odd lengths -/

theorem odd_length_mem {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := odd_length_mem_internal h hn hb

theorem odd_exists_iff {n : ℕ} (hn : Odd n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔ n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 :=
  odd_exists_iff_internal hn

/-! ### The structure of a Barker sequence of odd length -/

theorem aperiodic_eq {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 :=
  aperiodic_eq_internal h hn hb k hk0 hkn

theorem skew {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : Fin n) :
    h k * h (Fin.rev k) = (-1) ^ ((n - 1) / 2 + k.val) := skew_internal h hn hb k

theorem fold {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (w : ℕ) (hw : Even w)
    (hwn : w + 3 ≤ n) :
    ∑ k : Fin (w + 1), (-1) ^ k.val * h ⟨k.val, by omega⟩ * h ⟨w - k.val, by omega⟩ = 1 :=
  fold_internal h hn hb w hw hwn

theorem doubling {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (u : ℕ) (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) :
    h ⟨u - 1, by omega⟩ * h ⟨u, by omega⟩ = h ⟨2 * u - 1, by omega⟩ * h ⟨2 * u, by omega⟩ :=
  doubling_internal h hn hb u hu hun

theorem run_bounds {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (h7 : 7 ≤ n)
    (h01 : h ⟨0, by omega⟩ = h ⟨1, by omega⟩) (p q : ℕ)
    (hpn : p < n) (hpB : h ⟨p, hpn⟩ ≠ h ⟨p - 1, by omega⟩)
    (hpmin : ∀ s (hs0 : 0 < s) (hsp : s < p), h ⟨s, by omega⟩ = h ⟨s - 1, by omega⟩)
    (hqn : q < n) (hqB : h ⟨q, hqn⟩ ≠ h ⟨q - 1, by omega⟩) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s (hs0 : 0 < s) (hsq : s < q), h ⟨s, by omega⟩ ≠ h ⟨s - 1, by omega⟩ → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 :=
  run_bounds_internal h hn hb h7 h01 p q hpn hpB hpmin hqn hqB hpq hqmin

/-! ### The even reduction (Turyn–Storer, footnote 2) -/

theorem four_dvd_of_even {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n) (hb : IsBarker h) :
    4 ∣ n := four_dvd_of_even_internal h hn h2 hb

theorem existsRealCirculantHadamard_of_even {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n)
    (hb : IsBarker h) : ExistsRealCirculantHadamard n :=
  existsRealCirculantHadamard_of_even_internal h hn h2 hb

/-! ### The full classification, given the even half -/

theorem exists_iff_of_even
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 :=
  exists_iff_of_even_internal heven hn

theorem length_le_thirteen_of_even
    (heven : ∀ {n : ℕ} (h : Fin n → ℤ), 0 < n → Even n → IsBarker h → n = 2 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 :=
  length_le_thirteen_of_even_internal heven h hb

theorem exists_iff_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 :=
  exists_iff_of_circulantHadamard_internal hcirc hn

theorem length_le_thirteen_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 :=
  length_le_thirteen_of_circulantHadamard_internal hcirc h hb

end OddBarker
