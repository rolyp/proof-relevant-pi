module Transition.Concur.Properties where

   open import SharedModules

   open import Action.Concur using (_ᴬ⌣_)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_; TransitionFrom)
   open import Transition.Concur using (Concur₁)

   record ConcurrentWith {Γ} {P : Proc Γ} {a R} (E : P —[ a - _ ]→ R) : Set where
      field
         E† : TransitionFrom P
         {a†⌣a} : TransitionFrom.a E† ᴬ⌣ a
         E†⌣E : TransitionFrom.E E† ⌣₁[ a†⌣a ] E

   -- Whether E′ is the residual of another transition E† concurrent with E.
   blah : ∀ {Γ} {P : Proc Γ} {a R a′ S} (E : P —[ a - _ ]→ R) (E′ : R —[ a′ - _ ]→ S) → ConcurrentWith E
   blah = {!!}
