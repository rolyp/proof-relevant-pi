module Transition.Seq.Cofinal.Example where

   open import SharedModules

   open import Transition.Concur using (module Concur₁); open Concur₁
   open import Transition.Seq.Cofinal using (_≃_; module _≃_); open _≃_
   open import Transition.Seq.Example

   E⋆≃F⋆ : E⋆ ≃ F⋆
   E⋆≃F⋆ = E₁ ᶜ∶⇋∶ᶜ F₁ [ inj₁ (E⌣E′ │ᵥ F⌣F′) ]∷ []
