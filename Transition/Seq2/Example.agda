module Transition.Seq2.Example where

   open import Action as ᴬ using (); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (module _ᴬ⌣_); open _ᴬ⌣_
   open import Action.Seq2 as ᴬ⋆ using (); open ᴬ⋆.Action⋆
   open import Name using (Cxt; Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur; Delta′; module Delta′; ⊖)
   open import Transition.Seq2 as ᵀ⋆ using (_—[_]→⋆_); open ᵀ⋆._—[_]→⋆_

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

   open Delta′ hiding (S; S′)

   e : P │ Q —[ τ ᶜ - _ ]→ ν (R │ S)
   e = E │ᵥ F

   e′ : ν (R │ S) —[ τ ᶜ - _ ]→ _
   e′ = νᶜ (E′/E (⊖ E⌣E′) │• E′/E (⊖ F⌣F′))

   f : P │ Q —[ τ ᶜ - _ ]→ ν (R′ │ S′)
   f = E′ │ᵥ F′

   f′ : ν (R′ │ S′) —[ τ ᶜ - _ ]→ _
   f′ = νᶜ (E/E′ (⊖ E⌣E′) │• E/E′ (⊖ F⌣F′))

   E⋆ : P │ Q —[ [ τ ᶜ ] ⍮ [ τ ᶜ ] ]→⋆ _
   E⋆ = [ e ] ⍮ [ e′ ]

   F⋆ : P │ Q —[ [ τ ᶜ ] ⍮ [ τ ᶜ ] ]→⋆ _
   F⋆ = [ f ] ⍮ [ f′ ]
