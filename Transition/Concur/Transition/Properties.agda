module Transition.Concur.Transition.Properties where

   open import SharedModules

   open import Action using (_ᴬ⌣_)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁)
   open import Transition.Concur.Cofinal using (⊖₁-✓)
   open import Transition.Concur.Transition using (/-preserves-⌣₁′)

   open Delta′

   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (𝐸 : E ⌣₁[ 𝑎 ] E′) (𝐸′ : E′ ⌣₁[ 𝑎′ ] E″) (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
          let 𝐸′/E = /-preserves-⌣₁′ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′ in
          E/E′ (⊖₁ 𝐸′/E) ≅ E′/E (⊖₁ 𝐸/E″)
   blah _ _ _ = {!!}
