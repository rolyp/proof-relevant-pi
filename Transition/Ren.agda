-- A transition survives an arbitrary renaming.
module Transition.Ren where

   open import SharedModules

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren
   open import Proc.Ren
   open import Ren as ᴿ using (Ren; suc; pop; push; shift-*; swap; Renameable; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; action); open ᵀ._—[_-_]→_

   infixr 8 _*ᵇ_ _*ᶜ_
   _*ᶜ_ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P R} {a : Actionᶜ Γ} → P —[ a ᶜ - ι ]→ R → ρ * P —[ (ρ * a) ᶜ - ι ]→ ρ * R
   _*ᵇ_ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P R} {a : Actionᵇ Γ} → P —[ a ᵇ - ι ]→ R → ρ * P —[ (ρ * a) ᵇ - ι ]→ suc ρ * R

   ρ *ᶜ (• x 〈 y 〉∙ P) = • ρ * x 〈 ρ * y 〉∙ (ρ * P)
   ρ *ᶜ (E ➕₁ Q) = ρ *ᶜ E ➕₁ ρ * Q
   ρ *ᶜ (E ᶜ│ Q) = ρ *ᶜ E ᶜ│ ρ * Q
   ρ *ᶜ (P │ᶜ F) = ρ * P │ᶜ ρ *ᶜ F
   ρ *ᶜ (_│•_ {R = R} {y = y} E F) with ρ *ᵇ E
   ... | E′ rewrite pop-comm ρ y R = E′ │• ρ *ᶜ F
   ρ *ᶜ (_•│_ {S = S} {y = y} E F) with ρ *ᵇ F
   ... | F′ rewrite pop-comm ρ y S = ρ *ᶜ E •│ F′
   ρ *ᶜ (E │ᵥ F) = ρ *ᵇ E │ᵥ ρ *ᵇ F
   ρ *ᶜ (νᶜ_ {a = a} E) with suc ρ *ᶜ E
   ... | E′ rewrite push-comm ρ a = νᶜ E′
   ρ *ᶜ (! E) = ! (ρ *ᶜ E)

   ρ *ᵇ (x •∙ P) = (ρ * x) •∙ (suc ρ * P)
   ρ *ᵇ (E ➕₁ Q) = ρ *ᵇ E ➕₁ ρ * Q
   ρ *ᵇ (E ᵇ│ Q) with push * ρ * Q
   ... | _ rewrite push-comm ρ Q = ρ *ᵇ E ᵇ│ ρ * Q
   ρ *ᵇ (P │ᵇ F) with push * ρ * P
   ... | _ rewrite push-comm ρ P = ρ * P │ᵇ ρ *ᵇ F
   ρ *ᵇ (ν•_ {x = x} E) with suc ρ *ᶜ E; ... | E′ rewrite shift-* ρ x = ν• E′
   ρ *ᵇ (νᵇ_ {R = R} {a = a} E) with suc ρ *ᵇ E
   ... | E′ rewrite push-comm ρ a | sym (swap-suc-suc ρ R) = νᵇ E′
   ρ *ᵇ (! E) = ! (ρ *ᵇ E)
