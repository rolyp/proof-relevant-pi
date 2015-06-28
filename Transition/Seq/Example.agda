module Transition.Seq.Example where

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Name using (Cxt; Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_)

   -- Two extrusion-rendezvous traces, where the extrusions are of the same binder.
   postulate
      Γ : Cxt
      P Q : Proc Γ
      R R′ S S′ : Proc (Γ + 1)
      x u : Name Γ
      E : P —[ x • ᵇ - _ ]→ R
      E′ : P —[ u • ᵇ - _ ]→ R′
      F : Q —[ (• x) ᵇ - _ ]→ S
      F′ : Q —[ (• u) ᵇ - _ ]→ S′
      E⌣E′ : E ⌣[ ᵇ∇ᵇ ] E′
      F⌣F′ : F ⌣[ ᵛ∇ᵛ ] F′

   bibble : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   bibble = E │ᵥ F

   quibble : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   quibble = E′ │ᵥ F′
