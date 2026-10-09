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
`openai/math` in outline (Apache-2.0; see NOTICE); the proofs here are written for this repository except where
a docstring says it adapts one of those files.
-/

@[expose] public section

open Finset

namespace OddBarker

/-- The Challenge's `four_dvd_of_even`. -/
theorem four_dvd_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n)
    (hb : IsBarker h) : 4 ∣ n := by
  have hk2 : aperiodic h 2 = 0 :=
    even_shift_zero_of_even hb hn (k := 2) even_two (by omega) h2
  have hev : Even (n - 2) := by
    obtain ⟨u, hu⟩ := hn
    exact ⟨u - 1, by omega⟩
  have hkn : aperiodic h (n - 2) = 0 :=
    even_shift_zero_of_even hb hn (k := n - 2) hev (by omega) (by omega)
  have hd := aperiodic_add_aperiodic_sub_mod_four hb.1 (u := 2) (by omega) h2
  rw [hk2, hkn, add_zero, zero_sub, dvd_neg] at hd
  exact_mod_cast hd

/-- The periodic autocorrelation at shift `a` (the definition of `openai/math`'s `Barker/Model.lean`,
adapted). -/
def periodic {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, h j * h (j - a)

theorem periodic_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) :
    periodic h 0 = n := by
  unfold periodic
  have : ∀ j : Fin n, h j * h j = 1 := by
    intro j
    rcases hs j with h1 | h1 <;> rw [h1] <;> norm_num
  simp only [sub_zero, this]
  simp

set_option linter.unusedVariables false in
/-- `periodic h a = C(a) + C(n - a)` for `a ≠ 0` (the wraparound split). Adapts
`periodic_eq_aperiodic_add` of openai/math lean/OAI/LinearAlgebra/Barker/Wraparound.lean. -/
theorem periodic_eq_aperiodic_add {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) (ha : a ≠ 0) :
    periodic h a = aperiodic h a.val + aperiodic h (n - a.val) := by
  have ha_le : a.val ≤ n := Nat.le_of_lt a.isLt
  have hn : a.val + (n - a.val) = n := Nat.add_sub_of_le ha_le
  let f : Fin n → ℤ := fun j => h j * h (j - a)
  have split := Fin.sum_univ_add
    (fun j : Fin (a.val + (n - a.val)) => f (j.cast hn))
  rw [Fin.sum_congr' f hn] at split
  have low :
      (∑ j : Fin a.val, f ((Fin.castAdd (n - a.val) j).cast hn)) =
        aperiodic h (n - a.val) := by
    have hc : n - (n - a.val) = a.val := by omega
    have reindex : aperiodic h (n - a.val) =
        ∑ j : Fin a.val,
          h ⟨j.val, by omega⟩ * h ⟨j.val + (n - a.val), by omega⟩ := by
      unfold aperiodic
      apply Fintype.sum_equiv (finCongr hc)
      intro j
      rfl
    rw [reindex]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.castAdd (n - a.val) j).cast hn - a) =
        (⟨j.val + (n - a.val), by omega⟩ : Fin n) := by
      apply Fin.ext
      have hlt : (Fin.castAdd (n - a.val) j).cast hn < a := by
        change j.val < a.val
        exact j.isLt
      rw [Fin.coe_sub_iff_lt.mpr hlt]
      dsimp only [Fin.val_cast, Fin.val_castAdd]
      omega
    change h ((Fin.castAdd (n - a.val) j).cast hn) *
        h ((Fin.castAdd (n - a.val) j).cast hn - a) = _
    rw [hsub]
    rfl
  have high :
      (∑ j : Fin (n - a.val), f ((Fin.natAdd a.val j).cast hn)) =
        aperiodic h a.val := by
    unfold aperiodic
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.natAdd a.val j).cast hn - a) =
        (⟨j.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      have hle : a ≤ (Fin.natAdd a.val j).cast hn := by
        change a.val ≤ a.val + j.val
        omega
      rw [Fin.sub_val_of_le hle]
      dsimp only [Fin.val_cast, Fin.val_natAdd]
      omega
    change h ((Fin.natAdd a.val j).cast hn) *
        h ((Fin.natAdd a.val j).cast hn - a) = _
    rw [hsub, mul_comm]
    congr 1
    apply congrArg h
    apply Fin.ext
    change a.val + j.val = j.val + a.val
    omega
  change (∑ j : Fin n, f j) = _
  rw [split, low, high, add_comm]

/-- The periodic autocorrelation vanishes off the peak for an even Barker sequence of length `> 2`. Adapts
`periodic_offpeak_zero` of openai/math lean/OAI/LinearAlgebra/Barker/Main.lean. -/
theorem periodic_offpeak_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n)
    (h2 : 2 < n) (a : Fin n) (ha : a ≠ 0) : periodic h a = 0 := by
  have ha0 : 0 < a.val := by
    by_contra hnot
    apply ha
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hab := abs_le.mp (hb.2 a.val ha0 a.isLt)
  have hac := abs_le.mp (hb.2 (n - a.val) (by omega) (by omega))
  have hp := periodic_eq_aperiodic_add h a ha
  obtain ⟨u, hu⟩ := aperiodic_add_aperiodic_sub_mod_four hb.1 ha0 a.isLt
  obtain ⟨v, hv⟩ := four_dvd_of_even_internal h hn h2 hb
  have hv' : (n : ℤ) = 4 * v := by exact_mod_cast hv
  omega

/-- The circulant matrix of `h`: `circ h i j = h (j - i)`. -/
def circ {n : ℕ} (h : Fin n → ℤ) : RealMatrix n := fun i j => (h (j - i) : ℝ)

theorem circ_isCirculant {n : ℕ} (h : Fin n → ℤ) : IsCirculant (circ h) := by
  exact ⟨fun x => (h x : ℝ), fun i j => rfl⟩

theorem circ_isSignHadamard {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) (h2 : 2 < n) :
    IsSignHadamard (circ h) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · intro i j
    rcases hb.1 (j - i) with h1 | h1 <;> simp [circ, h1, IsSign]
  · ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, circ]
    have key : ∑ k, (h (k - i) : ℝ) * (h (k - j) : ℝ) = ((periodic h (j - i) : ℤ) : ℝ) := by
      unfold periodic
      push_cast
      apply Fintype.sum_equiv (Equiv.subRight i)
      intro k
      simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]
    rw [key]
    by_cases hij : i = j
    · subst hij
      simp [periodic_zero hb.1]
    · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
      simp [periodic_offpeak_zero hb hn h2 _ hji, hij]

/-- The Challenge's `existsRealCirculantHadamard_of_even`. -/
theorem existsRealCirculantHadamard_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n)
    (h2 : 2 < n) (hb : IsBarker h) : ExistsRealCirculantHadamard n := by
  exact ⟨circ h, circ_isCirculant h, circ_isSignHadamard hb hn h2⟩

/-- The even half from the circulant Hadamard statement. -/
theorem even_length_eq_two_or_four_of_circulantHadamard
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  by_cases hsmall : n ≤ 2
  · left
    obtain ⟨u, hu⟩ := hn
    omega
  · rcases hcirc n hnpos (existsRealCirculantHadamard_of_even_internal h hn (by omega) hb) with
      h1 | h1
    · obtain ⟨u, hu⟩ := hn
      omega
    · exact Or.inr h1

/-- The Challenge's `exists_iff_of_circulantHadamard`. -/
theorem exists_iff_of_circulantHadamard_internal
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (hn : 0 < n) :
    (∃ h : Fin n → ℤ, IsBarker h) ↔
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  exact exists_iff_of_even_internal
    (fun h hn he hb => even_length_eq_two_or_four_of_circulantHadamard hcirc h hn he hb) hn

/-- The Challenge's `length_le_thirteen_of_circulantHadamard`. -/
theorem length_le_thirteen_of_circulantHadamard_internal
    (hcirc : ∀ n : ℕ, 0 < n → ExistsRealCirculantHadamard n → n = 1 ∨ n = 4)
    {n : ℕ} (h : Fin n → ℤ) (hb : IsBarker h) : n ≤ 13 := by
  exact length_le_thirteen_of_even_internal
    (fun h hn he hb => even_length_eq_two_or_four_of_circulantHadamard hcirc h hn he hb) h hb

end OddBarker
