module Transition.Seq.Example where

   open import SharedModules

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (); open ᴬ⋆.Action⋆
   open import Name using (Cxt; Name; zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (suc; pop); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; Delta′; module Delta′; ⊖)
   open import Transition.Concur.Transition using (/-preserves-⌣)
   open import Transition.Ren
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
      𝐸 : E ⌣₁[ ᵇ∇ᵇ ] E′
      𝐸′ : E′ ⌣₁[ ᵇ∇ᵇ ] E″
      𝐸″ : E″ ⌣₁[ ᵇ∇ᵇ ] E
      𝐹 : F ⌣₁[ ᵛ∇ᵛ ] F′
      𝐹′ : F′ ⌣₁[ ᵛ∇ᵛ ] F″
      𝐹″ : F″ ⌣₁[ ᵛ∇ᵛ ] F

   E′/E = Delta′.E′/E (⊖ (inj₁ 𝐸))
   E/E′ = Delta′.E/E′ (⊖ (inj₁ 𝐸))
   F′/F = Delta′.E′/E (⊖ (inj₁ 𝐹))
   F/F′ = Delta′.E/E′ (⊖ (inj₁ 𝐹))

   E′/E/E″/E = Delta′.E′/E (⊖ (/-preserves-⌣ (inj₁ 𝐸) (inj₁ 𝐸′) (inj₁ 𝐸″)))
   E″/E/E′/E = Delta′.E/E′ (⊖ (/-preserves-⌣ (inj₁ 𝐸) (inj₁ 𝐸′) (inj₁ 𝐸″)))

   F′/F/F″/F = Delta′.E′/E (⊖ (/-preserves-⌣ (inj₁ 𝐹) (inj₁ 𝐹′) (inj₁ 𝐹″)))
   F″/F/F′/F = Delta′.E/E′ (⊖ (/-preserves-⌣ (inj₁ 𝐹) (inj₁ 𝐹′) (inj₁ 𝐹″)))

   P₁ = target E′/E
   P′₁ = target E/E′
   Q₁ = target F′/F
   Q′₁ = target F/F′

   P′ = target E′/E/E″/E
   Q′ = target F′/F/F″/F

   E₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   E₁ = E │ᵥ F

   E₂ : target E₁ —[ τ ᶜ - _ ]→ ν ((pop zero *) P₁ │ Q₁)
   E₂ = νᶜ (E′/E │• F′/F)

   E₃ : target E₂ —[ τ ᶜ - _ ]→ ν ((pop zero *) ((suc (pop zero) *) P′) │ Q′)
   E₃ = νᶜ ((pop zero *ᵇ) E′/E/E″/E │• F′/F/F″/F)

   E′₁ : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   E′₁ = E′ │ᵥ F′

   E′₂ : ν (R′ │ S′) —[ τ ᶜ - _ ]→ ν ((pop zero *) P′₁ │ Q′₁)
   E′₂ = νᶜ (E/E′ │• F/F′)

   E′₃ : target E′₂ —[ τ ᶜ - _ ]→ ν {!!}
   E′₃ = νᶜ {!!}

   E⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   E⋆ = E₁ ᶜ∷ E₂ ᶜ∷ E₃ ᶜ∷ []

   E′⋆ : P │ Q —[ τ ᶜ∷ τ ᶜ∷ [] ]→⋆ _
   E′⋆ = E′₁ ᶜ∷ E′₂ ᶜ∷ []
