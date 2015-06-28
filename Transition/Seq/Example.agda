module Transition.Seq.Example where

   open import SharedModules

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (); open ᴬ⋆.Action⋆
   open import Name using (Cxt; Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; Delta′; module Delta′; ⊖)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

   -- Two extrusion-rendezvous traces, where the extrusions are of the same binder.
   postulate
      Γ : Cxt
      P Q : Proc Γ
      R R′ S S′ : Proc (Γ + 1)
      x u : Name Γ
      E : P —[ x • ᵇ - _ ]→ R
      E′ : P —[ u • ᵇ - _ ]→ R′
      F : Q —[ (• x) ᵇ - _ ]→ S
      F′ : Q —[ (• u) ᵇ - _ ]→ S′
      E⌣E′ : E ⌣₁[ ᵇ∇ᵇ ] E′
      F⌣F′ : F ⌣₁[ ᵛ∇ᵛ ] F′

   open Delta′ hiding (S; S′)

   E₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   E₁ = E │ᵥ F

   E₂ : ν (R │ S) —[ τ ᶜ - _ ]→ _
   E₂ = νᶜ (E′/E (⊖ (inj₁ E⌣E′)) │• E′/E (⊖ (inj₁ F⌣F′)))

   F₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   F₁ = E′ │ᵥ F′

   F₂ : ν (R′ │ S′) —[ τ ᶜ - _ ]→ _
   F₂ = νᶜ (E/E′ (⊖ (inj₁ E⌣E′)) │• E/E′ (⊖ (inj₁ F⌣F′)))

   E⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   E⋆ = E₁ ᶜ∷ E₂ ᶜ∷ []

   F⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   F⋆ = F₁ ᶜ∷ F₂ ᶜ∷ []
