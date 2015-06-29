module Transition.Seq.Cofinal.Example where

   open import SharedModules

   open import Transition.Concur using (module Concur₁); open Concur₁
   open import Transition.Seq.Cofinal using (_≃_; module _≃_); open _≃_
   open import Transition.Seq.Example

   E⋆≃F⋆ : E⋆ ≃ E′⋆
   E⋆≃F⋆ =
      let blah = E₁ ᶜ∶⇋∶ᶜ E′₁ [ inj₁ (𝐸 │ᵥ 𝐹) ]∷ ? in
      {!!} --E₁ ᶜ∶⇋∶ᶜ E′₁ [ inj₁ (𝐸 │ᵥ 𝐹) ]∷ ?
