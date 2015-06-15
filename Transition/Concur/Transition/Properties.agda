module Transition.Concur.Transition.Properties where

   open import SharedModules

   open import Action using (_ᴬ⌣_)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁)

   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a″⌣a : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (𝐸 : E ⌣₁[ a⌣a′ ] E′) → E′ ⌣₁[ a′⌣a″ ] E″ → (𝐸″ : E″ ⌣₁[ a″⌣a ] E) → ⊥
   blah _ _ _ = ?
