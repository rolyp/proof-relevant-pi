module Transition.Concur.Properties2 where

   open import Action using (_ᴬ⌣_)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur; Delta′; ⊖; ⌣-sym)

   -- Residuation preserves concurrency.
   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a″⌣a : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (E⌣E′ : E ⌣[ a⌣a′ ] E′) → E′ ⌣[ a′⌣a″ ] E″ → (E″⌣E : E″ ⌣[ a″⌣a ] E) →
          Delta′.E′/E (⊖ E⌣E′) ⌣[ {!!} ] Delta′.E′/E (⊖ (⌣-sym E″⌣E))
   blah = {!!}
