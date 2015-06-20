-- Image of a cofinality braiding in a transition.
module Transition.Concur.Transition.Properties where

   open import SharedModules

   open import Action.Concur using (_ᴬ⌣_)
   open import Name using (zero)
   open import Proc using (Proc)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; Action₂; ᴬ⊖; ⊖₁)
   open import Transition.Concur.Cofinal using (⊖₁-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; module _Δ′_)
   open import Transition.Concur.Transition using (/-preserves-⌣₁′)

   open Delta′

   -- To be substantial, this theorem needs to be stated for the *symmetric* version of the relation.
   -- (See note on /-preserves-⌣₁′.)
   postulate
      /-preserves-cofin :
         ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
         {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
         (𝐸 : E ⌣₁[ 𝑎 ] E′) (𝐸′ : E′ ⌣₁[ 𝑎′ ] E″) (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
         let 𝐸′/E = /-preserves-⌣₁′ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′; open _Δ′_
         in E/E′ (⊖₁ 𝐸′/E) ≅ E/γ (⊖′[ (a″ , π₁ (ᴬ⊖ 𝑎″)) , zero ] (E′/E (⊖₁ 𝐸/E″)) (⊖₁-✓ 𝐸″))
