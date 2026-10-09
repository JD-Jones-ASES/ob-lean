module

public import OB.Fold
public import OB.KeyBound

/-!
# The run structure (Schmidt–Willms, Lemmas 3 and 4)

`a = seq h`, `n` odd, `n ≥ 7`, `a 0 = a 1`. A *sign change* is a position `s ≥ 1` with
`a s ≠ a (s - 1)`; `p` is the least one (`s₁` of the paper, the length of the first run) and `q` the
least one not divisible by `p` (`s_e`). Everything below uses only `skew_pair`, `doubling_seq` and
the signs:

* `2 ≤ p` (from `a 0 = a 1`); `2p ≤ n + 1` (`skew_pair` at `s = p - 1`: positions `1, …, p - 1` are
  not changes, so `n - 1, …, n - p + 1` are, and `n - p + 1 ≥ p`); `p` odd (`doubling_seq` at
  `u = p/2` would make `p/2` a change); so `3 ≤ p`;
* a change not divisible by `p` exists: `n - 1` and `n - 2` are changes (`skew_pair` at `s = 1, 2`)
  and `p ≥ 3` divides at most one of them (`exists_q`);
* `p < q`; `2q ≤ n + 3`: otherwise the windows `[1, q)` and `(n - q, n)` overlap in three consecutive
  positions `s, s + 1, s + 2`, each a change iff divisible by `p` (prefix) and a change iff `n - s`
  is not (`skew_pair`), so two of `n - s, n - s - 1, n - s - 2` are multiples of `p ≥ 3`;
  `q` odd (`doubling_seq` at `u = q/2`);
* `n ≤ p + q + 1` (`key_bound` with `fold_seq` at `p + q - 2` and `p + q`, if `p + q + 3 ≤ n`).
-/

@[expose] public section

open Finset

namespace OddBarker

/-- Four signs with `x y = -(z w)`: `y ≠ x ↔ w = z`. -/
theorem ru_sign4 {x y z w : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) (hw : w = 1 ∨ w = -1) (he : x * y = -(z * w)) : (y ≠ x ↔ w = z) := by
  revert he
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases hw with rfl | rfl <;> norm_num

/-- Four signs with `x y = z w`: `y ≠ x ↔ w ≠ z`. -/
theorem ru_sign4' {x y z w : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) (hw : w = 1 ∨ w = -1) (he : x * y = z * w) : (y ≠ x ↔ w ≠ z) := by
  revert he
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases hw with rfl | rfl <;> norm_num

/-- The mirror: `s` is a sign change iff `n - s` is not. -/
theorem ru_mirror {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s ≠ seq h (s - 1) ↔ seq h (n - s) = seq h (n - s - 1) :=
  ru_sign4 (seq_sign hb.1 (by omega : s - 1 < n)) (seq_sign hb.1 hsn)
    (seq_sign hb.1 (by omega : n - s - 1 < n)) (seq_sign hb.1 (by omega : n - s < n))
    (skew_pair hb hn hs1 (by omega))

/-- The mirror, other form: `s` is not a sign change iff `n - s` is. -/
theorem ru_mirror' {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s = seq h (s - 1) ↔ seq h (n - s) ≠ seq h (n - s - 1) := by
  have := ru_mirror hb hn hs1 hsn
  tauto

/-- Doubling: `u` is a sign change iff `2u` is. -/
theorem ru_double {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {u : ℕ} (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) : seq h u ≠ seq h (u - 1) ↔ seq h (2 * u) ≠ seq h (2 * u - 1) :=
  ru_sign4' (seq_sign hb.1 (by omega : u - 1 < n)) (seq_sign hb.1 (by omega : u < n))
    (seq_sign hb.1 (by omega : 2 * u - 1 < n)) (seq_sign hb.1 (by omega : 2 * u < n))
    (doubling_seq hb hn hu hun)

/-- Two multiples of `p ≥ 3` at distance `1` or `2` cannot exist. -/
theorem ru_dvd_close {p a b : ℕ} (hp : 3 ≤ p) (ha : p ∣ a) (hb : p ∣ b) (hab : a < b)
    (hba : b ≤ a + 2) : False := by
  have h1 := Nat.dvd_sub hb ha
  have h2 := Nat.le_of_dvd (by omega) h1
  omega

theorem two_le_p {n : ℕ} {h : Fin n → ℤ} (h01 : seq h 0 = seq h 1) {p : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) : 2 ≤ p := by
  by_contra hlt
  interval_cases p
  · exact hpB rfl
  · exact hpB h01.symm

set_option linter.unusedVariables false in
theorem two_mul_p_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    2 * p ≤ n + 1 := by
  by_contra hlt
  have h1 := (ru_mirror' hb hn (s := p - 1) (by omega) (by omega)).mp
    (hpmin (p - 1) (by omega) (by omega))
  have e1 : n - (p - 1) = n - p + 1 := by omega
  rw [e1] at h1
  exact h1 (hpmin (n - p + 1) (by omega) (by omega))

theorem p_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    Odd p := by
  have hp := two_mul_p_le hb hn h7 hpn hpB hpmin hp2
  rcases Nat.even_or_odd p with ⟨u, hu⟩ | ho
  · exfalso
    have e : 2 * u = p := by omega
    have hd := (ru_double hb hn (u := u) (by omega) (by omega)).mpr (by rw [e]; exact hpB)
    exact hd (hpmin u (by omega) (by omega))
  · exact ho

set_option linter.unusedVariables false in
/-- A sign change not divisible by `p` exists (`n - 1` or `n - 2`). -/
theorem exists_q {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p) :
    ∃ s, 0 < s ∧ s < n ∧ seq h s ≠ seq h (s - 1) ∧ ¬ p ∣ s := by
  have c1 := (ru_mirror' hb hn (s := 1) (by omega) (by omega)).mp (hpmin 1 (by omega) (by omega))
  have c2 := (ru_mirror' hb hn (s := 2) (by omega) (by omega)).mp (hpmin 2 (by omega) (by omega))
  by_cases hd : p ∣ n - 1
  · refine ⟨n - 2, by omega, by omega, c2, ?_⟩
    intro hd2
    exact ru_dvd_close hp3 hd2 hd (by omega) (by omega)
  · exact ⟨n - 1, by omega, by omega, c1, hd⟩

set_option linter.unusedVariables false in
theorem p_lt_q {n : ℕ} {h : Fin n → ℤ} {p q : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q) (hp2 : 2 ≤ p) : p < q := by
  rcases Nat.lt_or_ge p q with hlt | hge
  · exact hlt
  · exfalso
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · exact hpq (heq ▸ dvd_refl p)
    · rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; exact hqB rfl
      · exact hqB (hpmin q h0 hlt)

/-- For `t` and `n - t` both in `[1, q)`: `p` divides one of them. -/
theorem ru_either {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {p q t : ℕ}
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s)
    (ht1 : 1 ≤ t) (htq : t < q) (htn : t < n) (hmq : n - t < q) : p ∣ t ∨ p ∣ n - t := by
  by_cases hc : seq h t ≠ seq h (t - 1)
  · exact Or.inl (hqmin t (by omega) htq hc)
  · have hm := (ru_mirror' hb hn ht1 htn).mp (not_not.mp hc)
    exact Or.inr (hqmin (n - t) (by omega) hmq hm)

set_option linter.unusedVariables false in
theorem two_mul_q_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    2 * q ≤ n + 3 := by
  have hplq := p_lt_q hpB hpmin hqB hpq (by omega)
  by_contra hlt
  have H1 := ru_either hb hn hqmin (t := n - q + 1) (by omega) (by omega) (by omega) (by omega)
  have H2 := ru_either hb hn hqmin (t := n - q + 2) (by omega) (by omega) (by omega) (by omega)
  have H3 := ru_either hb hn hqmin (t := n - q + 3) (by omega) (by omega) (by omega) (by omega)
  rcases H1 with H1 | H1 <;> rcases H2 with H2 | H2 <;> rcases H3 with H3 | H3 <;>
    first
    | exact ru_dvd_close hp3 H1 H2 (by omega) (by omega)
    | exact ru_dvd_close hp3 H2 H1 (by omega) (by omega)
    | exact ru_dvd_close hp3 H1 H3 (by omega) (by omega)
    | exact ru_dvd_close hp3 H3 H1 (by omega) (by omega)
    | exact ru_dvd_close hp3 H2 H3 (by omega) (by omega)
    | exact ru_dvd_close hp3 H3 H2 (by omega) (by omega)

set_option linter.unusedVariables false in
theorem q_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hq : 2 * q ≤ n + 3) :
    Odd q := by
  have hplq := p_lt_q hpB hpmin hqB hpq (by omega)
  rcases Nat.even_or_odd q with ⟨u, hu⟩ | ho
  · exfalso
    obtain ⟨k, hk⟩ := hn
    have e : 2 * u = q := by omega
    have hd := (ru_double hb ⟨k, hk⟩ (u := u) (by omega) (by omega)).mpr (by rw [e]; exact hqB)
    have hdu := hqmin u (by omega) (by omega) hd
    exact hpq (e ▸ Dvd.dvd.mul_left hdu 2)
  · exact ho

set_option linter.unusedVariables false in
/-- Lemma 4: `n ≤ p + q + 1`. -/
theorem n_le_p_add_q_add_one {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) (hpodd : Odd p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hqodd : Odd q) (hplq : p < q) :
    n ≤ p + q + 1 := by
  by_contra hlt
  have hle : p + q + 3 ≤ n := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    obtain ⟨c, hc⟩ := hn
    omega
  have hw0 : Even (p + q - 2) := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    exact ⟨a + b, by omega⟩
  have hw2 : Even (p + q) := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    exact ⟨a + b + 1, by omega⟩
  have hT0 := fold_seq hb hn hw0 (by omega)
  have hT2 := fold_seq hb hn hw2 (by omega)
  exact key_bound (seq h) p q (fun i hi => seq_sign hb.1 (by omega)) hp2 hplq hpB
    (fun s hs1 hsp => hpmin s (by omega) hsp) hqB hpq
    (fun s hs1 hsq hc => hqmin s (by omega) hsq hc) hpodd hqodd hT0 hT2

/-- The run bounds on `ℕ`. -/
theorem run_bounds_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  have hp2 := two_le_p h01 hpB
  have hpodd := p_odd hb hn h7 hpn hpB hpmin hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hplq := p_lt_q hpB hpmin hqB hpq hp2
  have hq := two_mul_q_le hb hn h7 hpn hpB hpmin hp3 hqn hqB hpq hqmin
  have hqodd := q_odd hb hn h7 hpn hpB hpmin hp3 hqn hqB hpq hqmin hq
  exact ⟨hpodd, hqodd, hq,
    n_le_p_add_q_add_one hb hn h7 hpn hpB hpmin hp2 hpodd hqn hqB hpq hqmin hqodd hplq⟩

/-- The Challenge's `run_bounds`. -/
theorem run_bounds_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (h7 : 7 ≤ n)
    (h01 : h ⟨0, by omega⟩ = h ⟨1, by omega⟩) (p q : ℕ)
    (hpn : p < n) (hpB : h ⟨p, hpn⟩ ≠ h ⟨p - 1, by omega⟩)
    (hpmin : ∀ s (hs0 : 0 < s) (hsp : s < p), h ⟨s, by omega⟩ = h ⟨s - 1, by omega⟩)
    (hqn : q < n) (hqB : h ⟨q, hqn⟩ ≠ h ⟨q - 1, by omega⟩) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s (hs0 : 0 < s) (hsq : s < q), h ⟨s, by omega⟩ ≠ h ⟨s - 1, by omega⟩ → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  refine run_bounds_seq hb hn h7 ?_ hpn ?_ ?_ hqn ?_ hpq ?_
  · rw [seq_eq h (by omega : 0 < n), seq_eq h (by omega : 1 < n)]
    exact h01
  · rw [seq_eq h hpn, seq_eq h (by omega : p - 1 < n)]
    exact hpB
  · intro s hs0 hsp
    rw [seq_eq h (by omega : s < n), seq_eq h (by omega : s - 1 < n)]
    exact hpmin s hs0 hsp
  · rw [seq_eq h hqn, seq_eq h (by omega : q - 1 < n)]
    exact hqB
  · intro s hs0 hsq hc
    rw [seq_eq h (by omega : s < n), seq_eq h (by omega : s - 1 < n)] at hc
    exact hqmin s hs0 hsq hc

end OddBarker
