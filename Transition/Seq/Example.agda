module Transition.Seq.Example where

   open import SharedModules

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (); open ᴬ⋆.Action⋆
   open import Name using (Cxt; Name; zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (suc; pop); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur; Concur₁; module Concur₁; Delta′; module Delta′; ⊖); open Concur₁
   open import Transition.Ren
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

   -- Three concurrent extrusion-rendezvous, where the extrusions are of the same binder.
   -- TODO: show that the 6 interleavings of these are casually equivalent.
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
      𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′
      𝐸′ : E′ ⌣₁[ ᵇ∇ᵇ ] E″
      𝐸″ : E″ ⌣₁[ ᵇ∇ᵇ ] E
      𝐹 : F ⌣₁[ ˣ∇ˣ ] F′
      𝐹′ : F′ ⌣₁[ ˣ∇ˣ ] F″
      𝐹″ : F″ ⌣₁[ ˣ∇ˣ ] F

   E′/E = Delta′.E′/E (⊖ (inj₁ 𝐸))
   E″/E = Delta′.E/E′ (⊖ (inj₁ 𝐸″))
   F′/F = Delta′.E′/E (⊖ (inj₁ 𝐹))
   F″/F = Delta′.E/E′ (⊖ (inj₁ 𝐹″))
   P₁ = target E′/E
   Q₁ = target F′/F

   postulate
      𝐸′/E : E′/E ⌣[ ᵇ∇ᵇ ] E″/E
      𝐹′/F : F′/F ⌣[ ᶜ∇ᶜ ] F″/F

   E″/E/E′/E = Delta′.E′/E (⊖ 𝐸′/E)
   F″/F/F′/F = Delta′.E′/E (⊖ 𝐹′/F)

   P′ = target E″/E/E′/E
   Q′ = target F″/F/F′/F

   E₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   E₁ = E │ᵥ F

   E₂ : ν (R │ S)  —[ τ ᶜ - _ ]→ ν ((pop zero *) P₁ │ Q₁)
   E₂ = νᶜ (E′/E │• F′/F)

   E₃ : ν ((pop zero *) P₁ │ Q₁) —[ τ ᶜ - _ ]→ ν ((pop zero *) ((suc (pop zero) *) P′) │ Q′)
   E₃ = νᶜ ((pop zero *ᵇ) E″/E/E′/E │• F″/F/F′/F)

   E/E′ = Delta′.E/E′ (⊖ (inj₁ 𝐸))
   E″/E′ = Delta′.E′/E (⊖ (inj₁ 𝐸′))
   F/F′ = Delta′.E/E′ (⊖ (inj₁ 𝐹))
   F″/F′ = Delta′.E′/E (⊖ (inj₁ 𝐹′))
   P′₁ = target E/E′
   Q′₁ = target F/F′

   postulate
      𝐸″/E′ : E″/E′ ⌣[ ᵇ∇ᵇ ] E/E′
      𝐹″/𝐹′ : F″/F′ ⌣[ ᶜ∇ᶜ ] F/F′

   E″/E′/E/E′ = Delta′.E/E′ (⊖ 𝐸″/E′)
   F″/F′/F/F′ = Delta′.E/E′ (⊖ 𝐹″/𝐹′)

   P″ = target E″/E′/E/E′
   Q″ = target F″/F′/F/F′

   E′₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   E′₁ = E′ │ᵥ F′

   E′₂ : ν (R′ │ S′) —[ τ ᶜ - _ ]→ ν ((pop zero *) P′₁ │ Q′₁)
   E′₂ = νᶜ (E/E′ │• F/F′)

   E′₃ : ν ((pop zero *) P′₁ │ Q′₁) —[ τ ᶜ - _ ]→ ν ((pop zero *) ((suc (pop zero) *) P″) │ Q″)
   E′₃ = νᶜ ((pop zero *ᵇ) E″/E′/E/E′ │• F″/F′/F/F′)

   E⋆ : P │ Q —[ _ ]→⋆ _
   E⋆ = E₁ ᶜ∷ E₂ ᶜ∷ E₃ ᶜ∷ []

   E′⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   E′⋆ = E′₁ ᶜ∷ E′₂ ᶜ∷ E′₃ ᶜ∷ []
