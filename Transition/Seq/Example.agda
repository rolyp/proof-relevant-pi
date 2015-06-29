module Transition.Seq.Example where

   open import SharedModules

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (); open ᴬ⋆.Action⋆
   open import Name using (Cxt; Name; zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (pop); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; Delta′; module Delta′; ⊖)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

   -- Three concurrent extrusion-rendezvous, where the extrusions are of the same binder.
   postulate
      Γ : Cxt
      P Q : Proc Γ
      R R′ R″ S S′ S″ : Proc (Γ + 1)
      x y z : Name Γ
      E : P —[ x • ᵇ - _ ]→ R
      E′ : P —[ y • ᵇ - _ ]→ R′
      E″ : P —[ z • ᵇ - _ ]→ R″
      F : Q —[ (• x) ᵇ - _ ]→ S
      F′ : Q —[ (• y) ᵇ - _ ]→ S′
      F″ : Q —[ (• z) ᵇ - _ ]→ S″
      E⌣E′ : E ⌣₁[ ᵇ∇ᵇ ] E′
      E′⌣E″ : E′ ⌣₁[ ᵇ∇ᵇ ] E″
      E″⌣E : E″ ⌣₁[ ᵇ∇ᵇ ] E
      F⌣F′ : F ⌣₁[ ᵛ∇ᵛ ] F′
      F′⌣F″ : F′ ⌣₁[ ᵛ∇ᵛ ] F″
      F″⌣F : F″ ⌣₁[ ᵛ∇ᵛ ] F

   E′/E = Delta′.E′/E (⊖ (inj₁ E⌣E′))
   E/E′ = Delta′.E/E′ (⊖ (inj₁ E⌣E′))
   F′/F = Delta′.E′/E (⊖ (inj₁ F⌣F′))
   F/F′ = Delta′.E/E′ (⊖ (inj₁ F⌣F′))

   E₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   E₁ = E │ᵥ F

   P₁ : Proc _
   P₁ = Delta′.S (⊖ (inj₁ E⌣E′))

   Q₁ : Proc _
   Q₁ = Delta′.S (⊖ (inj₁ F⌣F′))

   E₂ : target E₁ —[ τ ᶜ - _ ]→ ν ((pop zero *) P₁ │ Q₁)
   E₂ = νᶜ (E′/E │• F′/F)

   E₃ : target E₂ —[ τ ᶜ - _ ]→ _
   E₃ = νᶜ {!? │• ?!}

   F₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   F₁ = E′ │ᵥ F′

   F₂ : ν (R′ │ S′) —[ τ ᶜ - _ ]→ _
   F₂ = νᶜ (E/E′ │• F/F′)

   E⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   E⋆ = E₁ ᶜ∷ E₂ ᶜ∷ []

   F⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   F⋆ = F₁ ᶜ∷ F₂ ᶜ∷ []
