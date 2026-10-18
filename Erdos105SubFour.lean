/-
Proof of `Erdos105.erdos_105.variants.sub_four` (google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/105.lean, pinned to commit e754a78c, 2026-10-17), stated in the
post-#6762 form (no answer slot): the answer to the question is NO, so the statement proved is the
negation of the declaration's proposition.

Counterexample (Core_65536, erdosproblems.com forum thread 105, 24 Jul 2026): ten points A and six
points B with integer coordinates such that A ∩ B = ∅, |A| = |B| + 4, A is not collinear, and every
line through two points of A contains a point of B. The 45 pairs are checked by exact integer
arithmetic (`decide`).

Produced by an automated Lean prover (Claude Opus 5.5 via Claude Code, 2026-10-18, run 1018_1542,
5 minutes wall-clock) given the counterexample as a hint, and checked by `#print axioms`
(propext, Classical.choice, Quot.sound).
-/
import FormalConjectures.ErdosProblems.«105»

open EuclideanGeometry

namespace Erdos105

noncomputable def e105f (p : ℤ × ℤ) : ℝ² := !₂[(p.1 : ℝ), (p.2 : ℝ)]

lemma e105f_inj : Function.Injective e105f := by
  intro p q h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [e105f] at h0 h1
  exact Prod.ext h0 h1

lemma e105_mem (a b c : ℤ × ℤ) (hab : a ≠ b)
    (h : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0) :
    e105f c ∈ line[ℝ, e105f a, e105f b] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  have hR : ((b.1 - a.1 : ℤ) : ℝ) * ((c.2 - a.2 : ℤ) : ℝ) - ((b.2 - a.2 : ℤ) : ℝ) * ((c.1 - a.1 : ℤ) : ℝ) = 0 := by
    exact_mod_cast h
  push_cast at hR
  by_cases hx : b.1 = a.1
  · have hy : b.2 ≠ a.2 := fun hy => hab (Prod.ext hx.symm hy.symm)
    have hyR : ((b.2 : ℝ) - a.2) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hy)
    have hxR : (b.1 : ℝ) = a.1 := by exact_mod_cast hx
    have hc : (c.1 : ℝ) = a.1 := by
      rw [hxR] at hR
      have : ((b.2 : ℝ) - a.2) * ((c.1 : ℝ) - a.1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hyR
      · linarith
    refine ⟨((c.2 : ℝ) - a.2) / ((b.2 : ℝ) - a.2), ?_⟩
    ext i
    fin_cases i
    · simp [e105f, AffineMap.lineMap_apply, hxR, hc]
    · simp [e105f, AffineMap.lineMap_apply]
      field_simp
      ring
  · have hxR : ((b.1 : ℝ) - a.1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx)
    refine ⟨((c.1 : ℝ) - a.1) / ((b.1 : ℝ) - a.1), ?_⟩
    ext i
    fin_cases i
    · simp [e105f, AffineMap.lineMap_apply]
      field_simp
      ring
    · simp [e105f, AffineMap.lineMap_apply]
      field_simp
      linear_combination (-1 : ℝ) * hR

lemma e105_noncol (a b c : ℤ × ℤ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0) :
    ¬ Collinear ℝ ({e105f a, e105f b, e105f c} : Set ℝ²) := by
  intro hcol
  have hab : e105f a ≠ e105f b := by
    intro he
    have := e105f_inj he
    subst this
    simp at h
  have hm := hcol.mem_affineSpan_of_mem_of_ne (p₃ := e105f c) (by simp) (by simp) (by simp) hab
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hm
  obtain ⟨r, hr⟩ := hm
  have h0 := congrArg (fun v : ℝ² => v 0) hr
  have h1 := congrArg (fun v : ℝ² => v 1) hr
  simp [e105f, AffineMap.lineMap_apply] at h0 h1
  apply h
  have : ((b.1 : ℝ) - a.1) * ((c.2 : ℝ) - a.2) - ((b.2 : ℝ) - a.2) * ((c.1 : ℝ) - a.1) = 0 := by
    rw [← h0, ← h1]; ring
  exact_mod_cast this

def e105A : List (ℤ × ℤ) := [(168,0),(280,560),(280,140),(420,630),(360,240),(504,672),(280,-280),(420,0),(840,840),(0,-840)]
def e105B : List (ℤ × ℤ) := [(0,420),(840,3360),(336,336),(280,0),(420,315),(-840,-2520)]

lemma e105_key : ∀ p ∈ e105A, ∀ q ∈ e105A, p ≠ q → ∃ c ∈ e105B,
    (q.1 - p.1) * (c.2 - p.2) - (q.2 - p.2) * (c.1 - p.1) = 0 := by decide

/-- The `n − 4` variant of Erdős problem 105 is false: the configuration above is a counterexample. -/
theorem erdos_105_variants_sub_four :
    ¬ ∀ A B : Finset ℝ², Disjoint A B → A.card = B.card + 4 →
      ¬ Collinear ℝ (A : Set ℝ²) →
      ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q] := by
  intro h
  have hd : Disjoint (e105A.toFinset.image e105f) (e105B.toFinset.image e105f) := by
    rw [Finset.disjoint_image e105f_inj]; decide
  have hc : (e105A.toFinset.image e105f).card = (e105B.toFinset.image e105f).card + 4 := by
    rw [Finset.card_image_of_injective _ e105f_inj, Finset.card_image_of_injective _ e105f_inj]
    decide
  have hn : ¬ Collinear ℝ ((e105A.toFinset.image e105f : Finset ℝ²) : Set ℝ²) := by
    intro hcol
    apply e105_noncol (168,0) (280,560) (280,140) (by decide)
    apply hcol.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [Finset.mem_coe, Finset.mem_image]
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, by decide, rfl⟩
    · exact ⟨_, by decide, rfl⟩
    · exact ⟨_, by decide, rfl⟩
  obtain ⟨p, hp, q, hq, hpq, hb⟩ := h _ _ hd hc hn
  rw [Finset.mem_image] at hp hq
  obtain ⟨p', hp', rfl⟩ := hp
  obtain ⟨q', hq', rfl⟩ := hq
  rw [List.mem_toFinset] at hp' hq'
  have hne : p' ≠ q' := fun e => hpq (congrArg e105f e)
  obtain ⟨c, hcB, hcr⟩ := e105_key p' hp' q' hq' hne
  exact hb (e105f c) (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hcB))
    (e105_mem p' q' c hne hcr)

end Erdos105

#print axioms Erdos105.erdos_105_variants_sub_four
