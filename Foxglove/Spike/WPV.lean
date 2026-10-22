module

public import Foxglove.Rules.WP.Post
public import Foxglove.Rules.WP.Counterexamples

/-! # Spike: is the value-level `wp` a lax weakest precondition?

Throwaway, not for upstreaming.  Lean core's `Std.WP.WPMonad` asks of
`wp : m α → (α → Pred) → Pred` monotonicity, `post a ⊑ wp (pure a) post`, and the lax bind law
`wp x (fun a ↦ wp (f a) post) ⊑ wp (x >>= f) post`.  Foxglove's `wp` takes postconditions over
the result *random variable*; its value-level shadow is
`wpV t Q := wp t (fun X ↦ valuePost X Q)`.

Finding: on *convex* postconditions (Amaryllis's strongly convex assertions: laws, sure facts,
pure facts, closed under `∧` and `∀`), `wpV` satisfies all three laws and stays convex
(`wpV_mono`, `wpV_pure`, `wpV_bind`, `convex_wpV`).  So the convex fragment is a lax core WP;
`WPBind_counterexample` shows the RV-level bind rule needs convexity. -/

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra
open UpperSetBI
open Iris BI UpperSetBI OURAProp

noncomputable section

/-- The value-level weakest precondition: the result has some law, and on the fibre at each
value `v` the postcondition `Q v` holds. -/
def wpV {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (Q : α → FProp) : FProp :=
  wp t (fun X ↦ valuePost X Q)

/-! ## Convexity of value-level postconditions -/

/-- A sure fact next to a convex assertion is convex: sure facts leave every conditioning
(`SURE_STR_CONVEX`). -/
lemma convex_liftPred_sep_left {E : RV Prop} {P : FProp} (hP : Convex P) :
    Convex iprop(⌈E⌉ ∗ P) := fun ν ↦
  (C_CONS fun _ ↦ sep_comm.1).trans <| SURE_STR_CONVEX.trans (sep_mono_right (hP ν))

/-- **A value-level postcondition is convex when each fibre's is.**  Conditioning a
`valuePost` fuses the two conditionings (`C_SKOLEM`, `C_FUSE`); reordering the pair
(`C_TRANSF`) and projecting onto the value (`C_PROJ_OF_CONVEX`) recovers a single conditioning
on the value, which is again a `valuePost`. -/
theorem convex_valuePost {α : Type} {X : RV α} {Q : α → FProp} (hQ : ∀ a, Convex (Q a)) :
    Convex (valuePost X Q) := by
  intro γ μ
  unfold valuePost
  refine (C_SKOLEM (Q := fun p : γ × PMF α ↦
      iprop(𝒞⟨p.2⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x)))).trans ?_
  refine exists_elim fun κ ↦ ?_
  refine (C_FUSE (K := fun p : γ × α ↦ iprop(⌈fun ρ ↦ X ρ = p.2⌉ ∗ Q p.2))).1.trans ?_
  set μ₁ : PMF (γ × α) := fuse μ κ
  set μ₂ : PMF (α × γ) := PMF.map Prod.swap μ₁
  have hbij : Set.BijOn Prod.swap μ₂.support μ₁.support := by
    rw [PMF.support_map]
    refine ⟨?_, Prod.swap_injective.injOn, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      simpa using hp
    · intro p hp
      exact ⟨p.swap, ⟨p, hp, rfl⟩, Prod.swap_swap p⟩
  have hval : ∀ b ∈ μ₂.support, μ₂ b = μ₁ b.swap := by
    intro b _
    rw [PMF.map_apply, tsum_eq_single b.swap]
    · simp
    · intro p hp
      rw [ite_eq_right]
      intro h
      exact hp (by rw [h, Prod.swap_swap])
  refine (C_TRANSF (f := Prod.swap) (K := fun p : γ × α ↦
      iprop(⌈fun ρ ↦ X ρ = p.2⌉ ∗ Q p.2)) hbij hval).trans ?_
  refine (C_PROJ_OF_CONVEX (μ := μ₂) (K := fun a : α ↦ iprop(⌈fun ρ ↦ X ρ = a⌉ ∗ Q a))
    fun a ↦ convex_liftPred_sep_left (hQ a)).trans ?_
  exact exists_intro (Ψ := fun ν : PMF α ↦ iprop(𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x))) _

/-! ## The three laws of a lax weakest precondition -/

variable {α β : Type} [Inhabited α] [Inhabited β]
  {m : Type → Type} [Monad m] [Interp.LawfulBernoulliInterpretable m]

/-- **Monotonicity.** -/
theorem wpV_mono {t : m α} {Q Q' : α → FProp} (h : ∀ a, Q a ⊢ Q' a) : wpV t Q ⊢ wpV t Q' :=
  WP_CONS fun _ ↦ valuePost_mono h

/-- **The pure law.**  A constant result has the point-mass law, and on its one fibre the
postcondition is given (`C_UNIT_L`), next to the free sure fact that the constant is itself. -/
theorem wpV_pure {a : α} {Q : α → FProp} : Q a ⊢ wpV (pure a : m α) Q := by
  refine entails_trans ?_ WP_PURE
  refine entails_trans ?_ (exists_intro (Ψ := fun ν : PMF α ↦
    iprop(𝒞⟨ν⟩ x; (⌈fun ρ ↦ (fun _ : Ω ↦ a) ρ = x⌉ ∗ Q x))) (PMF.pure a))
  refine entails_trans ?_ (C_UNIT_L (v₀ := a)
    (K := fun x ↦ iprop(⌈fun ρ ↦ (fun _ : Ω ↦ a) ρ = x⌉ ∗ Q x))).2
  exact emp_sep.2.trans (sep_mono_left (liftPred_of_forall fun _ ↦ rfl))

/-- **The lax bind law, for convex postconditions** (`WP_BIND`, whose side conditions
`aeProper_valuePost` and `convex_valuePost` discharge). -/
theorem wpV_bind {C : m α} {F : α → m β} {Q : β → FProp} (hQ : ∀ b, Convex (Q b)) :
    wpV C (fun a ↦ wpV (F a) Q) ⊢ wpV (C >>= F) Q :=
  WP_BIND (aeProper_valuePost Q) fun _ ↦ convex_valuePost hQ

/-- **`wpV` stays in the convex fragment**: a conditioning outside `wp` moves inside
(`C_WP_SWAP`) and collapses there (`convex_valuePost`). -/
theorem convex_wpV {t : m α} {Q : α → FProp} (hQ : ∀ a, Convex (Q a)) :
    Convex (wpV t Q) := fun ν ↦
  (C_WP_SWAP fun _ ↦ aeProper_valuePost Q).trans
    (WP_CONS fun _ ↦ convex_valuePost hQ ν)

end

end Foxglove
