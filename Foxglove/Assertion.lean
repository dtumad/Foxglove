module

import Foxglove.Basic
public import Foxglove.Algebra.PSpace
public import Foxglove.Algebra.OURA
public import Foxglove.Interp.Bernoulli.Basic
public import Iris.ProofMode

@[expose] public section
namespace Foxglove

open ProbSpace
open Iris OrderedUnitalResourceAlgebra

noncomputable section

/-! # The assertions of Foxglove

Resources are bounded-footprint probability spaces on the tape, and assertions are upper sets
of them (`FProp`).  This file defines the connectives the rules speak about: ownership,
joint conditioning `𝒞⟨μ⟩ v; K v`, having a law `E ~ μ`, sure facts `⌈E⌉`, and the weakest
precondition `wp`. -/

abbrev FProp := Iris.UpperSetBI.OURAProp (BoundedFootprintSpace Bool)

instance : Iris.BI FProp := inferInstance

open UpperSetBI

section

open ProbabilityTheory

def own {M} [OrderedUnitalResourceAlgebra M] (b : M) : OURAProp M := UpperSetBI.own b

/-- Owning the unit costs nothing: `emp` and `own 1` are the same upper set. -/
lemma own_one {M} [OrderedUnitalResourceAlgebra M] : ⊢ (own (1 : M) : OURAProp M) :=
  fun _ _ h ↦ h

def ownP (p : PSpace Ω) : FProp :=
  iprop(∃ h : HasBoundedFootprint (p : PSp Ω), own ⟨(p : PSp Ω), h⟩)

open Iris.BI in
lemma ownP_one : ⊢ ownP 1 := by
  unfold ownP
  refine entails_trans ?_ (exists_intro hasBoundedFootprint_one)
  exact own_one

/-- `p` satisfies `P`: `p` is a resource, and owning exactly `p` establishes `P`.  In the
upper-set model this is `p ∈ P`. -/
def satP (p : PSpace Ω) (P : FProp) : Prop :=
  ∃ h : HasBoundedFootprint (p : PSp Ω),
    own (⟨(p : PSp Ω), h⟩ : BoundedFootprintSpace Bool) ⊢ P

/-- **Joint conditioning** (Bluebell, Def. 4.11; Amaryllis, §3.3): a space `m` that is the
`μ`-mixture of a kernel `κ`, whose fibres `κ v`, for `v` in the support, each satisfy `K v`
once owned. -/
def jointConditioning {A : Type} (μ : PMF A) (K : A → FProp) : FProp :=
  iprop(
    ∃ m : PSpace Ω,
    ∃ κ : TrivialMarkovKernel A m,
      ownP m ∗
      ⌜m.μ = (μ.toMeasureWithMs ⊤).bind κ⌝ ∗
      ∀ v : μ.support, ownP (κ v) -∗ K v
  )

/-- Precedence 36: above `⊢`/`⊣⊢` (29) and `∗`, so that `𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v` and
`P ∗ 𝒞⟨μ⟩ v; K v` parse as intended. -/
notation:36 "𝒞" "⟨" μ "⟩" v:arg ";" K:36 => jointConditioning μ (fun v => iprop(K))

/-- `E` has the law `μ`: some owned space pushes `E` forward to `μ`. -/
def hasDistribution {A : Type} (E : RV A) (μ : PMF A) : FProp :=
  iprop(
    ∃ P : PSpace Ω,
      ownP P ∗
      ⌜
        have Eμ := @P.μ.map Ω A P.ms ⊤ E
        almostMeasurable E P ∧ Eμ = μ.toMeasureWithMs ⊤
      ⌝
  )

notation:100 E:100 " ~ " p:100 => hasDistribution E p

/-- The pair of two random variables. -/
scoped notation:70 E₁:71 " ×ᵣ " E₂:71 => fun s => (E₁ s, E₂ s)

/-- **Sure facts** `⌈E⌉`: some owned space gives the failure set of `E` measure zero. -/
class LiftPred (α : Type) where
  lift : (Ω → α) → FProp

instance : LiftPred Prop where
  lift a := iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

instance : LiftPred Bool where
  lift a := iprop(∃ P : PSpace Ω, ownP P ∗ ⌜P.μ {ρ | ¬ a ρ} = 0⌝)

class LiftUnary (β : Type) where
  lift : β → Ω → Prop

instance : LiftUnary (RV Prop) := ⟨fun a ω ↦ a ω⟩

instance : LiftUnary (RV Bool) := ⟨fun E ω ↦ E ω = true⟩

instance : LiftUnary Prop := ⟨fun p _ ↦ p⟩

instance : LiftUnary Bool := ⟨fun p _ ↦ p = true⟩

class LiftBinary (α β : Type) where
  lift : α → β → Ω → Prop

instance {α : Type} : LiftBinary (RV α) α where
  lift := fun l r ω ↦ l ω = r

instance {α : Type} : LiftBinary α (RV α) where
  lift := fun l r ω ↦ l = r ω

instance {α : Type} : LiftBinary (RV α) (RV α) where
  lift := fun l r ω ↦ l ω = r ω

instance {ι γ : Type} : LiftBinary (ι → RV γ) (ι → γ) where
  lift := fun x v ω ↦ ∀ i, x i ω = v i

class LiftMem (α β : Type) where
  lift : α → β → Ω → Prop

instance {α : Type} : LiftMem (RV α) (Set α) where
  lift := fun E S ω ↦ E ω ∈ S

syntax "lift(" term ", " term ")" : term

macro_rules
  | `(lift(¬$a, $ρ))            => `(¬lift($a, $ρ))
  | `(lift($a ∧ $b, $ρ))        => `(lift($a, $ρ) ∧ lift($b, $ρ))
  | `(lift($a ∨ $b, $ρ))        => `(lift($a, $ρ) ∨ lift($b, $ρ))
  | `(lift($a → $b, $ρ))        => `(lift($a, $ρ) → lift($b, $ρ))
  | `(lift($a = $b, $ρ))        => `(LiftBinary.lift $a $b $ρ)
  | `(lift(∀ $x:ident, $b, $ρ)) => `(∀ $x:ident, lift($b, $ρ))
  | `(lift(∃ $x:ident, $b, $ρ)) => `(∃ $x:ident, lift($b, $ρ))
  | `(lift($a ∈ $b, $ρ))        => `(LiftMem.lift $a $b $ρ)
  | `(lift(($x), $ρ))           => `(lift($x, $ρ))
  | `(lift($x, $ρ))             => `(LiftUnary.lift $x $ρ)

syntax (name := liftStx) (priority := high) "⌈" term "⌉" : term

macro_rules (kind := liftStx)
  | `(⌈$t⌉) => `(LiftPred.lift fun ω ↦ lift($t, ω))

section

open Lean PrettyPrinter Delaborator SubExpr Elab Term

@[app_unexpander LiftPred.lift]
meta def unexpLiftPred : Unexpander
  | `($_ fun $_ ↦ $pred) => do `(⌈$pred⌉) 
  | `($_) => throw ()

@[delab app.Foxglove.LiftBinary.lift]
meta def unexpLiftBinary : Delab := do
  let expr ← getExpr
  let_expr Foxglove.LiftBinary.lift _ _ _ lhs rhs _ := expr | failure
  `($(←delab lhs) = $(←delab rhs))

@[delab app.Foxglove.LiftUnary.lift]
meta def unexpLiftUnary : Delab := do
  let expr ← getExpr
  let_expr Foxglove.LiftUnary.lift _ _ x _ := expr | failure
  `($(←delab x))

end

/-- Assertions of the shape `∃ P, ownP P ∗ ⌜φ P⌝` -- the shape `hasDistribution` and
`liftPred` share -- with pointwise equivalent side conditions are the same assertion. -/
theorem ownP_pure_congr {φ ψ : PSpace Ω → Prop} (h : ∀ P, φ P ↔ ψ P) :
    (iprop(∃ P : PSpace Ω, ownP P ∗ ⌜φ P⌝) : FProp)
      = iprop(∃ P : PSpace Ω, ownP P ∗ ⌜ψ P⌝) := by
  have hfe : φ = ψ := funext fun P ↦ propext (h P)
  rw [hfe]

/-- A postcondition split along the value of `X`: condition on a law `ν` of `X`, and on the
fibre at `x` the result surely is `x` and `Q x` holds.  Sequencing uses this shape to hand a
continuation the value it receives. -/
def valuePost {α : Type} (X : RV α) (Q : α → FProp) : FProp :=
  iprop(∃ ν : PMF α, 𝒞⟨ν⟩ x; (⌈fun ρ ↦ X ρ = x⌉ ∗ Q x))

/-! ### `wp` and its locality clause

`wp t Q` holds of a resource `a` when, from any ambient footprint `μ₀` containing `a` beside a
frame `c`, running `t` yields a witness `b` beside the same frame inside the run's footprint,
satisfying `Q` of the run's result.  The witness may measure no more than `a` could, together
with the randomness the run added (`freshMs`): this *locality clause* makes the witnesses
produced at the fibres of a conditioning comparable, which `C_WP_SWAP` and `WP_BIND_C` need in
order to assemble them into one resource.  It is an upper bound, so upward closure is
unaffected. -/

/-- The σ-algebra a resource measures.  `⊤` on the undefined resource, which keeps `msOf`
monotone and makes the clause below vacuous there. -/
@[instance_reducible]
def msOf (x : BoundedFootprintSpace Bool) : MeasurableSpace Ω :=
  match (x : PSp Ω) with
  | none => ⊤
  | some p => p.ms

lemma msOf_mono {x y : BoundedFootprintSpace Bool} (hxy : x ≤ y) : msOf x ≤ msOf y := by
  unfold msOf
  cases hx : (x : PSp Ω) with
  | none =>
    have hy : (y : PSp Ω) = none := by
      refine PSp.ge_top_imp_top ?_
      rw [show (⊤ : PSp Ω) = (x : PSp Ω) from by rw [hx]; rfl]
      exact hxy
    rw [hy]
  | some p =>
    cases hy : (y : PSp Ω) with
    | none => exact le_top
    | some q =>
      have hle : (x : PSp Ω) ≤ (y : PSp Ω) := hxy
      rw [hx, hy] at hle
      exact (WithTop.coe_le_coe.1 hle).1

/-- A defined product measures exactly what its two factors measure between them: the
independent product's σ-algebra is the join.  Needed wherever a witness is multiplied by a
frame and `wp`'s locality clause has to be re-established. -/
lemma msOf_mul_le {x y : BoundedFootprintSpace Bool} (h : ✓(x * y)) :
    msOf (x * y) ≤ msOf x ⊔ msOf y := by
  obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (valid_mul h))
  obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp (valid_mul_r h))
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (PSp.valid_def.mp h)
  have hmul : PSp.mul ((x : PSp Ω)) ((y : PSp Ω)) = (s : PSp Ω) := hs
  rw [hx', hy'] at hmul
  unfold msOf
  rw [hs, hx', hy']
  exact le_of_eq (PSp.mul_inversion hmul).1

open Interp Interp.ProbTree Iris.BI OURAProp in
/-- **Weakest precondition**, with the locality clause `msOf b ≤ msOf a ⊔ freshMs …`. -/
def wp {α : Type} [Inhabited α] {m : Type → Type} [Interp.BernoulliInterpretable m]
    (t : m α) (Q : RV α → FProp) : FProp :=
  fmk {
    carrier := {a |
      ∀ (μ₀ : BoundedFootprintPsp) (c : BoundedFootprintSpace Bool),
        ✓μ₀.psp → a * c ≤ μ₀.toSpace →
        ∃ b : BoundedFootprintSpace Bool,
          b * c ≤ (run t μ₀).1.toSpace ∧ ✓b ∧
            msOf b ≤ msOf a ⊔ freshMs μ₀ (Interp.BernoulliInterpretable.interp t) ∧
            (own b ⊢ Q (result (run t μ₀)))}
    upper' := by
      intro x y hxy hx μ₀ c hv hle
      obtain ⟨b, hb1, hb2, hb3, hb4⟩ := hx μ₀ c hv (le_trans (mul_le_mul_right_le hxy c) hle)
      exact ⟨b, hb1, hb2, le_trans hb3 (sup_le_sup_right (msOf_mono hxy) _), hb4⟩
  }

/-- A postcondition `⦃X, Q⦄`, the assertion `Q` about the result `X`. Scoped: unscoped, the `⦃`
token would also capture core's `Std.WP` triple notation `⦃P⦄ x ⦃Q⦄`. -/
scoped macro "⦃" x:Lean.Parser.Term.funBinder ", " Q:term "⦄" : term => `(fun $x ↦ iprop($Q))

open Lean PrettyPrinter Delaborator SubExpr Elab Term in
@[app_unexpander wp]
meta def unexpWp : Unexpander
  | `($_ $t $Q) => do
    match Q with
    | `(fun $x ↦ iprop($y)) => `($(mkIdent `wp) $t ⦃$x, $y⦄)
    | _                     => `($(mkIdent `wp) $t $Q)
  | `($_) => throw ()

end

section

open Iris BI UpperSetBI OURAProp

noncomputable def ftrue : FProp := fmk UpperSetBI.true

noncomputable def ffalse : FProp := fmk UpperSetBI.false

variable {P Q R : FProp}

/-! ### What `FProp` satisfies as a BI -/

/-- `1` sits below every resource (`PSp.one_le`), so `emp` is the whole upper set and the
logic is affine: resources may always be thrown away.  Through iris-lean's generic instance
this also makes every `FProp` `Absorbing`. -/
instance : BIAffine FProp where
  affine P := ⟨by induction P using Quotient.ind; exact fun _ _ _ ↦ PSp.one_le⟩

/-- `<pers> P` holds either of everything or of nothing, according to whether `P` already
holds of the unit resource, so `Persistent P` says exactly that owning nothing suffices for
`P`.  Neither `Persistent` nor `Intuitionistic` therefore holds of a general `FProp`: for a
valid `b`, `own b` is persistent exactly when `b ≤ 1`.  The persistent fragment is the one iris-lean already covers with `pure_persistent`
and `emp_persistent`. -/
lemma persistent_iff {U : UpperSet (BoundedFootprintSpace Bool)} :
    Persistent (fmk U) ↔ ∀ m, ✓m → m ∈ U → (1 : BoundedFootprintSpace Bool) ∈ U :=
  ⟨fun h ↦ h.persistent, fun h ↦ ⟨h⟩⟩

attribute [grind .] and_intro entails_rfl pure_intro or_intro_l or_intro_r or_elim
                    Iris.BI.BIBase.pure and_elim_l and_elim_r Iris.BI.BIBase.BiEntails.mk

attribute [grind cases] Iris.BI.BIBase.BiEntails

attribute [grind →] entails_trans

@[simp, grind .]
lemma entails_ftrue : P ⊢ ftrue := pure_intro True.intro

@[simp, grind .]
lemma ffalse_entails : ffalse ⊢ P := by
  apply pure_elim'
  grind

end

open Lean Elab Term in
/--
We steal Iris entails parser.
-/
scoped elab:25 (priority := high) P:term:29 " ⊢ " Q:term:25 : term => do
  let s ← saveState
  let pointwise ←
    try
      let ty ← instantiateMVars (← Meta.inferType (← withoutErrToSorry (elabTerm P none)))
      pure ty.isArrow
    catch _ =>
      pure false
  s.restore -- `elabTerm` does who-knows-what to the environment but I just want to see the type
  let stx ←
    if pointwise
    then
      `(∀ a, ($P) a ⊢ ($Q) a)
    else
      `(
        Iris.BI.BIBase.Entails iprop($P) iprop($Q)
      )
  elabTerm stx .none

end

end Foxglove
