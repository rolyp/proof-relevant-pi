-- (Partial) monoid of traces.
module Transition.Seq2 where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (Action₂)
   open import Action.Seq2 as ᴬ⋆ using (Action⋆; Action⋆↱; Action⋆↲; inc⋆); open ᴬ⋆.Action⋆
   open import Action.Seq2.Ren using (ren-preserves-inc⋆; ren-preserves-inc⋆-assoc)
   open import Name using (Cxt; Name; _+_; +-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Ren as ᴿ using (_ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (braid; ⋈[_,_,_]; ⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_)

   -- Use APL's ⍮ for diagrammatic-order composition, since Unicode's only useful semicolon is already reserved.
   infixr 9 _⍮_

   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [_] : ∀ {a R} → P —[ a - _ ]→ R → P —[ [ a ] ]→⋆ R
      -- Monoid operations.
      [] : P —[ [] ]→⋆ P
      _⍮_ : ∀ {a⋆ R a′⋆ S} → P —[ a⋆ ]→⋆ R → R —[ a′⋆ ]→⋆ S →
            P —[ a⋆ ⍮ a′⋆ ]→⋆ Proc↱ (+-assoc Γ (inc⋆ a⋆) (inc⋆ a′⋆)) S

   source⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc Γ
   source⋆ {P = P} _ = P

   target⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   target⋆ {R = R} _ = R

   action⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Action⋆ Γ
   action⋆ {a⋆ = a⋆} _ = a⋆
