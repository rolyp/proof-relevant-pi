-- Traces are lists of composable transitions. Snoc lists might be closer to execution, which grows to the right.
-- Concatenation/append proved unmanageable when defining ≃ (heterogeneous equality was very difficult).
module Transition.Seq where

   open import ProofRelevantPiCommon

   open import Action using (_ᵇ; _ᶜ)
   open import Action.Seq using (Action⋆; module Action⋆; inc⋆); open Action⋆
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

   src⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc Γ
   src⋆ {P = P} _ = P

   action⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Action⋆ Γ
   action⋆ {a⋆ = a⋆} _ = a⋆

   tgt⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   tgt⋆ {R = R} _ = R
