module

public import OB.Identity

/-!
# Schmidt–Willms's Lemma 4 in sign-change form

`p` is the first sign change (`a p ≠ a (p - 1)`, with no change before it), `q` the first sign change
not divisible by `p`; both odd, `2 ≤ p < q`. If the folded sum `T0` takes the value `1` at both
`p + q - 2` and `p + q`, contradiction: in the step identity the only sign-change pairs summing to
`p + q` are `(p, q)` and `(q, p)`, so the sum is `±8` while `|2 a 0 Δ| ≤ 4`. Only the signs of `a` on
`[0, p + q]` are used. Ported from the bench probes of 2026-10-06 (lane K2).
-/

@[expose] public section

open Finset

namespace OddBarker

theorem key_bound (a : ℕ → ℤ) (p q : ℕ)
    (hs : ∀ i, i ≤ p + q → a i = 1 ∨ a i = -1)
    (hp2 : 2 ≤ p) (hpq : p < q)
    (hpb : a p ≠ a (p - 1)) (hpmin : ∀ s, 1 ≤ s → s < p → a s = a (s - 1))
    (hqb : a q ≠ a (q - 1)) (hndvd : ¬ p ∣ q)
    (hqmin : ∀ s, 1 ≤ s → s < q → a s ≠ a (s - 1) → p ∣ s)
    (hpodd : Odd p) (hqodd : Odd q)
    (hT0 : T0 a (p + q - 2) = 1) (hT2 : T0 a (p + q) = 1) : False := by
  have hw : Even (p + q - 2) := by
    obtain ⟨u, hu⟩ := hpodd
    obtain ⟨v, hv⟩ := hqodd
    exact ⟨u + v, by omega⟩
  have hstep := T0_step a hw
  have e : p + q - 2 + 2 = p + q := by omega
  rw [e, hT0, hT2] at hstep
  set w := p + q - 2 with hwdef
  set f : ℕ → ℤ := fun t => (-1) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t)) with hf
  have hzero : ∀ t ∈ range (w + 1), t ≠ p - 1 → t ≠ q - 1 → f t = 0 := by
    intro t ht h1 h2
    simp only [Finset.mem_range] at ht
    by_cases hA : a (t + 1) = a t
    · simp [hf, hA]
    by_cases hB : a (w - t + 1) = a (w - t)
    · simp [hf, hB]
    exfalso
    have hs1 : p ≤ t + 1 := by
      by_contra hlt
      exact hA (by simpa using hpmin (t + 1) (by omega) (by omega))
    have hs2 : p ≤ w - t + 1 := by
      by_contra hlt
      have := hpmin (w - t + 1) (by omega) (by omega)
      exact hB (by simpa using this)
    have hq1 : t + 1 < q := by omega
    have hq2 : w - t + 1 < q := by omega
    have d1 := hqmin (t + 1) (by omega) hq1 (by simpa using hA)
    have d2 := hqmin (w - t + 1) (by omega) hq2 (by simpa using hB)
    have hdv : p ∣ (t + 1) + (w - t + 1) := Nat.dvd_add d1 d2
    have e3 : (t + 1) + (w - t + 1) = p + q := by omega
    rw [e3] at hdv
    exact hndvd ((Nat.dvd_add_right (dvd_refl p)).mp hdv)
  have hmemp : p - 1 ∈ range (w + 1) := by simp; omega
  have hmemq : q - 1 ∈ range (w + 1) := by simp; omega
  have hne : p - 1 ≠ q - 1 := by omega
  have hsum : ∑ t ∈ range (w + 1), f t = f (p - 1) + f (q - 1) :=
    Finset.sum_eq_add_of_mem (p - 1) (q - 1) hmemp hmemq hne
      (fun c hc hcc => hzero c hc hcc.1 hcc.2)
  have hp1 : Even (p - 1) := by
    obtain ⟨u, hu⟩ := hpodd
    exact ⟨u, by omega⟩
  have hq1 : Even (q - 1) := by
    obtain ⟨u, hu⟩ := hqodd
    exact ⟨u, by omega⟩
  have ep1 : p - 1 + 1 = p := by omega
  have eq1 : q - 1 + 1 = q := by omega
  have ew1 : w - (p - 1) = q - 1 := by omega
  have ew2 : w - (q - 1) = p - 1 := by omega
  have hfp : f (p - 1) = (a p - a (p - 1)) * (a q - a (q - 1)) := by
    simp only [hf, ep1, ew1, eq1, hp1.neg_one_pow, one_mul]
  have hfq : f (q - 1) = (a q - a (q - 1)) * (a p - a (p - 1)) := by
    simp only [hf, ep1, ew2, eq1, hq1.neg_one_pow, one_mul]
  have hsum' : ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t))
      = (a p - a (p - 1)) * (a q - a (q - 1)) + (a q - a (q - 1)) * (a p - a (p - 1)) := by
    rw [← hfp, ← hfq, ← hsum]
  rw [hsum'] at hstep
  have ew1' : w + 1 = p + q - 1 := by omega
  have ew2' : w + 2 = p + q := by omega
  rw [ew1'] at hstep
  have hap := hs p (by omega)
  have hap1 := hs (p - 1) (by omega)
  have haq := hs q (by omega)
  have haq1 := hs (q - 1) (by omega)
  have ha0 := hs 0 (by omega)
  have haw1 := hs (p + q - 1) (by omega)
  have haw2 := hs (p + q) (by omega)
  rcases hap with h1 | h1 <;> rcases hap1 with h2 | h2 <;> rcases haq with h3 | h3 <;>
    rcases haq1 with h4 | h4 <;> rcases ha0 with h5 | h5 <;> rcases haw1 with h6 | h6 <;>
    rcases haw2 with h7 | h7 <;> simp only [h1, h2, h3, h4, h5, h6, h7, ne_eq, not_true_eq_false] at hstep hpb hqb <;>
    (try norm_num at hstep) <;> (try norm_num at hpb) <;> (try norm_num at hqb)

end OddBarker
