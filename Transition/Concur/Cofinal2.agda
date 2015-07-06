module Transition.Concur.Cofinal2 where

   open import SharedModules

   open import Action as ᴬ using (inc); open ᴬ.Action
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖)
   open import Name using (_+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (suc; push); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_; target)
   open import Transition.Concur using (Concur₁; module Concur₁); open Concur₁

   syntax Cofin 𝐸 P P′ = P ⋈[ 𝐸 ] P′

   data Cofin {Γ} : ∀ {P : Proc Γ} {a a′} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
               (𝐸 : E ⌣₁[ 𝑎 ] E′) → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in Proc Γ′ → Proc Γ′ → Set where
      blah : ∀ {P : Proc Γ} {Q R S a a′} (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) →
             Cofin (E ᵇ│ᵇ F)
                   ((push *) (target E) │ (suc push *) (target F))
                   ((suc push *) (target E) │ (push *) (target F))
