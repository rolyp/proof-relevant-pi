-- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
-- composition is probably what we eventually want.
module Transition.Seq where

   open import SharedModules

   open import Action using (_ᵇ; _ᶜ)
   open import Action.Seq using (Action⋆; inc⋆; []; _ᵇ∷_; _ᶜ∷_)
   open import Name using (_+_; +-assoc)
   open import Proc using (Proc; Proc↱)
   open import Transition using (_—[_-_]→_)

   infixr 5 _ᵇ∷_ _ᶜ∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _ᵇ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᵇ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᵇ∷ a⋆ ]→⋆ Proc↱ (+-assoc _ _ (inc⋆ a⋆)) S
      _ᶜ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᶜ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᶜ∷ a⋆ ]→⋆ Proc↱ (+-assoc _ _ (inc⋆ a⋆)) S

   infixl 0 _—[_]→⋆_

   target⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   target⋆ {R = R} _ = R
