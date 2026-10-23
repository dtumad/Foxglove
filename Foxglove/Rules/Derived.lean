module

public import Foxglove.Rules
public import Foxglove.Rules.WP.Post
public import Foxglove.Interp.Bernoulli.Split
public import Foxglove.Algebra.UniformPMF

/-! # Derived rules for laws

Consequences of the rules for the most common specification shape, a law `⦃X, X ~ ν⦄`:

* `wp_pure_law`, `wp_bind_law`, `wp_bind_pure`: laws of `pure`, of sequencing, and of a sampler
  followed by a deterministic continuation;
* `wp_exists_law_of_wp`, `wp_exists_law_mono`: packaging a law into, and weakening, a law
  description `⦃X, ∃ μ, ⌜P μ⌝ ∗ X ~ μ⦄`;
* `wp_split`: rejection sampling `split n` is uniform, from its tape law (`WP_SAMP`).
-/

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris BI UpperSetBI OURAProp
open Interp

noncomputable section

section Laws

variable {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m]
  {α β : Type} [Inhabited α] [Inhabited β]

/-- **The law of `pure`** is the Dirac law: `WP_PURE` and `DISTR_DIRAC`. -/
theorem wp_pure_law (x : α) : ⊢ wp (pure x : m α) ⦃X, X ~ δ x⦄ := by
  iapply (WP_PURE (Q := fun Y ↦ Y ~ δ x))
  exact DISTR_DIRAC

/-- **Sequencing two samplers.**  The law of `C >>= F` is the law of `C` bound with the laws
of the continuations: `WP_BIND_COND` at the law of `C`, `C_BIND` to recollect the fibres. -/
theorem wp_bind_law {C : m α} {F : α → m β} {ν : PMF α} {κ : α → PMF β}
    (hC : ⊢ wp C ⦃X, X ~ ν⦄) (hF : ∀ v, ⊢ wp (F v) ⦃Y, Y ~ κ v⦄) :
    ⊢ wp (C >>= F) ⦃Y, Y ~ ν.bind κ⦄ := by
  have hfib : ∀ (X : RV α) (v : α), (⌈X = v⌉ : FProp) ⊢ ⌈X = v⌉ ∗ wp (F v) ⦃Y, Y ~ κ v⦄ := by
    intro X v
    iintro H
    isplitl [H]
    · iexact H
    · exact hF v
  iapply (WP_CONS fun Y ↦ C_BIND (μ := ν) (κ := κ) (X := Y))
  iapply (WP_BIND_COND (ν := ν) fun v ↦ aeProper_hasDistribution (κ v))
  iapply (WP_CONS fun X ↦ entails_trans (C_UNIT_R (E := X) (μ := ν)).1 (C_CONS (hfib X)))
  exact hC

/-- **Sequencing with a deterministic continuation.**  A sampler followed by a pure function
reports the push-forward of the sampler's law. -/
theorem wp_bind_pure {C : m α} {ν : PMF α} (g : α → β) (hC : ⊢ wp C ⦃X, X ~ ν⦄) :
    ⊢ wp (C >>= fun x ↦ pure (g x)) ⦃Y, Y ~ ν.map g⦄ := by
  rw [← PMF.bind_pure_comp g ν]
  exact wp_bind_law hC fun v ↦ wp_pure_law (g v)

end Laws

section Descriptions

variable {m : Type → Type} [Monad m] [LawfulBernoulliInterpretable m] {α : Type} [Inhabited α]
  {t : m α}

/-- **A law satisfying `P` describes the program**: package `⦃X, X ~ ν⦄` and `P ν` as the law
description `⦃X, ∃ μ, ⌜P μ⌝ ∗ X ~ μ⦄`. -/
theorem wp_exists_law_of_wp {ν : PMF α} {P : PMF α → Prop} (h : ⊢ wp t ⦃X, X ~ ν⦄)
    (hP : P ν) : ⊢ wp t ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄ := by
  refine entails_trans h (WP_CONS fun X ↦ ?_)
  iintro H
  iexists ν
  isplitl []
  · ipureintro
    exact hP
  · iexact H

/-- **Weakening a law description.** -/
theorem wp_exists_law_mono {P P' : PMF α → Prop} (h : ⊢ wp t ⦃X, ∃ μ : PMF α, ⌜P μ⌝ ∗ X ~ μ⦄)
    (hPP' : ∀ μ, P μ → P' μ) : ⊢ wp t ⦃X, ∃ μ : PMF α, ⌜P' μ⌝ ∗ X ~ μ⦄ := by
  refine entails_trans h (WP_CONS fun X ↦ ?_)
  iintro ⟨%μ, %hμ, H⟩
  iexists μ
  isplitl []
  · ipureintro
    exact hPP' μ hμ
  · iexact H

end Descriptions

/-- **Rejection sampling is uniform**: `split n` has the uniform law on `Fin (n + 1)`, read off
its tape law (`lawOf_split`) by `WP_SAMP`. -/
theorem wp_split (n : ℕ) : ⊢ wp (split n) ⦃X, X ~ PMF.uniformOfFintype' (Fin (n + 1))⦄ :=
  Proofs.WP_SAMP (split n) _ fun i ↦ by simp [lawOf_split]

end

end Foxglove
