module Transition.Concur.Cofinal2 where

   open import SharedModules

   open import Action using (inc)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖)
   open import Name using (_+_)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁)

   data ⋈[_] : ∀ {Γ} {P : Proc Γ} {a a′} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
               (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in Proc Γ′ → Proc Γ′ → Set where
