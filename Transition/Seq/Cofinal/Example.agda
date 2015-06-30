module Transition.Seq.Cofinal.Example where

   open import SharedModules

   open import Action as ᴬ; open ᴬ.Actionᵇ; open ᴬ.Action
   open import Action.Seq as ᴬ⋆; open ᴬ⋆.Action⋆
   open import Name using (zero)
   open import Proc as ᴾ; open ᴾ.Proc
   open import Ren as ᴿ using (pop); open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (module Concur₁; Delta′; module Delta′; ⊖); open Concur₁
   open import Transition.Concur.Cofinal using (⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (_Δ′_; ⊖′[_,_])
   open import Transition.Concur.Transition.Properties using (/-preserves-cofin)
   open import Transition.Seq as ᵀ⋆; open ᵀ⋆._—[_]→⋆_
   open import Transition.Seq.Cofinal using (_≃_; module _≃_; _Δ_; ⊖⋆[_,_]); open _≃_
   open import Transition.Seq.Example

   E⋆≃F⋆ : E⋆ ≃ E′⋆
   E⋆≃F⋆ =
      let 𝐸₁ = inj₁ (𝐸 │ᵥ 𝐹)
          _ Δ E₃∷[]/γ = ⊖⋆[ (τ ᶜ , τ ᶜ) , zero ] (E₃ ᶜ∷ []) (⊖-✓ 𝐸₁)
          bib : E₁ ᶜ∷ Delta′.E′/E (⊖ 𝐸₁) ᶜ∷ E₃ ᶜ∷ [] ≃ E′₁ ᶜ∷ Delta′.E/E′ (⊖ 𝐸₁) ᶜ∷ E₃∷[]/γ
          bib = E₁ ᶜ∶⇋∶ᶜ E′₁ [ 𝐸₁ ]∷ (E₃ ᶜ∷ [])
          E′₃∷[] : target E′₂ —[ τ ᶜ∷ [] ]→⋆ _
          E′₃∷[] = E′₃ ᶜ∷ []
          gib : E₃∷[]/γ ≅ E′₃∷[]
          gib = {!!}
          E₃/γ : ν ((pop zero *) P′₁ │ Q′₁) —[ τ ᶜ - _ ]→ {!!}
          E₃/γ = _Δ′_.E/γ (⊖′[ (τ ᶜ , τ ᶜ) , zero ] E₃ (⊖-✓ 𝐸₁))
          nib : E′₃ ≅ E₃/γ
          nib = {!!}
      in {!!}
