module Transition.Concur.Properties where

   open import SharedModules

   open import Action as ᴬ using (Action; inc; _ᴬ⌣_); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ._ᴬ⌣_
   open import Name using (zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (Ren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
   open import Transition.Concur using (ᴬ⊖; Concur₁; module Concur₁; Delta′; Delta; ⊖₁; ⌣-sym); open Concur₁

   -- Only in the two ᵛ∇ᵛ cases is the outcome not uniquely determined by the types; in each case
   -- extrusions of the same binder are preserved.
   /-preserves-ᴬ⌣ : ∀ {Γ} {a a′ a″ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) (a′⌣a″ : a′ ᴬ⌣ a″) (a⌣a″ : a ᴬ⌣ a″) →
         π₁ (ᴬ⊖ a⌣a′) ᴬ⌣ π₁ (ᴬ⊖ a⌣a″)
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵛ∇ᵛ ᵛ∇ᵛ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵛ∇ᵛ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵇ∇ᵇ ᵛ∇ᵛ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵇ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵇ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵛ∇ᵛ ᵛ∇ᵛ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵛ∇ᵛ ᵇ∇ᵇ = ᵛ∇ᵛ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᵇ ᵛ∇ᵛ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᵇ ᵇ∇ᵇ = ᵇ∇ᵇ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᶜ ᵇ∇ᶜ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᵇ ᵛ∇ᵛ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵛ∇ᵛ ᶜ∇ᵇ = ᵛ∇ᵛ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵇ∇ᵇ ᶜ∇ᵇ = ᵇ∇ᵇ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵇ∇ᶜ ᶜ∇ᶜ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᶜ∇ᵇ ᶜ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᶜ∇ᶜ ᶜ∇ᶜ = ᶜ∇ᶜ

   -- Concurrent actions are preserved by renamings.
   _*ᴬ⌣ : ∀ {Γ Γ′} {a a′ : Action Γ} (ρ : Ren Γ Γ′) (a⌣a′ : a ᴬ⌣ a′) → (ρ *) a ᴬ⌣ (ρ *) a′
   (ρ *ᴬ⌣) ᵛ∇ᵛ = ᵛ∇ᵛ
   (ρ *ᴬ⌣) ᵇ∇ᵇ = ᵇ∇ᵇ
   (ρ *ᴬ⌣) ᵇ∇ᶜ = ᵇ∇ᶜ
   (ρ *ᴬ⌣) ᶜ∇ᵇ = ᶜ∇ᵇ
   (ρ *ᴬ⌣) ᶜ∇ᶜ = ᶜ∇ᶜ

   _*ᵇᵇ⌣ : ∀ {Γ Γ′} {P : Proc Γ} {a a′ R R′} {a⌣a′ : a ᵇ ᴬ⌣ a′ ᵇ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′}
          (ρ : Ren Γ Γ′) → E ⌣₁[ a⌣a′ ] E′ → (ρ *ᵇ) E ⌣₁[ (ρ *ᴬ⌣) a⌣a′ ] (ρ *ᵇ) E′
   _*ᶜᶜ⌣ : ∀ {Γ Γ′} {P : Proc Γ} {a a′ R R′} {a⌣a′ : a ᶜ ᴬ⌣ a′ ᶜ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′}
          (ρ : Ren Γ Γ′) → E ⌣₁[ a⌣a′ ] E′ → (ρ *ᶜ) E ⌣₁[ (ρ *ᴬ⌣) a⌣a′ ] (ρ *ᶜ) E′
   _*ᶜᵇ⌣ : ∀ {Γ Γ′} {P : Proc Γ} {a a′ R R′} {a⌣a′ : a ᶜ ᴬ⌣ a′ ᵇ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′}
          (ρ : Ren Γ Γ′) → E ⌣₁[ a⌣a′ ] E′ → (ρ *ᶜ) E ⌣₁[ (ρ *ᴬ⌣) a⌣a′ ] (ρ *ᵇ) E′
   _*ᵇᶜ⌣ : ∀ {Γ Γ′} {P : Proc Γ} {a a′ R R′} {a⌣a′ : a ᵇ ᴬ⌣ a′ ᶜ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′}
          (ρ : Ren Γ Γ′) → E ⌣₁[ a⌣a′ ] E′ → (ρ *ᵇ) E ⌣₁[ (ρ *ᴬ⌣) a⌣a′ ] (ρ *ᶜ) E′

   (ρ *ᵇᵇ⌣) (_ᵇ│ᵇ_ {P = P} {Q} E F) rewrite ᴿ+-comm 1 ρ Q | ᴿ+-comm 1 ρ P = (ρ *ᵇ) E ᵇ│ᵇ (ρ *ᵇ) F
   (ρ *ᵇᵇ⌣) (E⌣E′ ➕₁ Q) = (ρ *ᵇᵇ⌣) E⌣E′ ➕₁ _
   (ρ *ᵇᵇ⌣) (P │ᵇᵇ F⌣F′) rewrite ᴿ+-comm 1 ρ P = (ρ *) P │ᵇᵇ (ρ *ᵇᵇ⌣) F⌣F′
   (ρ *ᵇᵇ⌣) (E⌣E′ ᵇᵇ│ Q) rewrite ᴿ+-comm 1 ρ Q = (ρ *ᵇᵇ⌣) E⌣E′ ᵇᵇ│ (ρ *) Q
   (ρ *ᵇᵇ⌣) (ν• E⌣E′) = ν• (suc ρ *ᶜᶜ⌣) E⌣E′
   (ρ *ᵇᵇ⌣) (ν•ᵇ_ {R = R} {R′} {a} {E} {E′} E⌣E′) with (suc ρ *ᵇ) E′ | (suc ρ *ᶜᵇ⌣) E⌣E′
   ... | _ | suc-ρ*E⌣E′ rewrite ᴿ+-comm 1 ρ a | sym (swap-suc-suc ρ R′) = ν•ᵇ suc-ρ*E⌣E′
   (ρ *ᵇᵇ⌣) (νᵇᵇ_ {R = R} {R′} {a} {a′} {E} {E′} E⌣E′) with (suc ρ *ᵇ) E | (suc ρ *ᵇ) E′ | (suc ρ *ᵇᵇ⌣) E⌣E′
   ... | _ | _ | suc-ρ*E⌣E′
      rewrite ᴿ+-comm 1 ρ a | sym (swap-suc-suc ρ R) | ᴿ+-comm 1 ρ a′ | sym (swap-suc-suc ρ R′) = νᵇᵇ suc-ρ*E⌣E′
   (ρ *ᵇᵇ⌣) (νᵛᵛ_ {R = R} {R′} {x} {u} {E} {E′} E⌣E′) with (suc ρ *ᵇ) E | (suc ρ *ᵇ) E′ | (suc ρ *ᵇᵇ⌣) E⌣E′
   ... | E† | E‡ | suc-ρ*E⌣E′
      rewrite ᴿ+-comm 1 ρ (• x) | sym (swap-suc-suc ρ R) | ᴿ+-comm 1 ρ (• u) | sym (swap-suc-suc ρ R′) = νᵛᵛ suc-ρ*E⌣E′
   (ρ *ᵇᵇ⌣) (! E⌣E′) = ! (ρ *ᵇᵇ⌣) E⌣E′

   (ρ *ᶜᵇ⌣) (E ᶜ│ᵇ F) = {!!}
   (ρ *ᶜᵇ⌣) (E⌣E′ ➕₁ Q) = (ρ *ᶜᵇ⌣) E⌣E′ ➕₁ _
   (ρ *ᶜᵇ⌣) (! E⌣E′) = ! (ρ *ᶜᵇ⌣) E⌣E′

   _*ᵇᶜ⌣ ρ (E ᵇ│ᶜ F) = {!!}
   _*ᵇᶜ⌣ ρ (E⌣E′ │•ᵇ F) = {!!}
   _*ᵇᶜ⌣ ρ (E ᵇ│• E⌣E′) = {!!}
   _*ᵇᶜ⌣ ρ (E⌣E′ │ᵥᵇ F) = {!!}
   _*ᵇᶜ⌣ ρ (E ᵇ│ᵥ E⌣E′) = {!!}
   _*ᵇᶜ⌣ ρ (E⌣E′ ➕₁ Q) = {!!}
   _*ᵇᶜ⌣ ρ (P │ᵇᶜ E⌣E′) = {!!}
   _*ᵇᶜ⌣ ρ (E⌣E′ ᵇᶜ│ Q) = {!!}
   _*ᵇᶜ⌣ ρ (ν•ᶜ E⌣E′) = {!!}
   _*ᵇᶜ⌣ ρ (νᵇᶜ E⌣E′) = {!!}
   _*ᵇᶜ⌣ ρ (! E⌣E′) = {!!}

   (ρ *ᶜᶜ⌣) (E ᶜ│ᶜ F) = (ρ *ᶜ) E ᶜ│ᶜ (ρ *ᶜ) F
   (ρ *ᶜᶜ⌣) (_│•ᶜ_ {y = y} {R′ = R′} E⌣E′ F) rewrite pop-comm ρ y R′ = (ρ *ᶜᵇ⌣) E⌣E′ │•ᶜ (ρ *ᶜ) F
   (ρ *ᶜᶜ⌣) (_ᶜ│•_ {y = y} {R = R} E F⌣F′) rewrite pop-comm ρ y R = (ρ *ᵇ) E ᶜ│• (ρ *ᶜᶜ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (E⌣E′ │ᵥᶜ F) = (ρ *ᶜᵇ⌣) E⌣E′ │ᵥᶜ (ρ *ᵇ) F
   (ρ *ᶜᶜ⌣) (E ᶜ│ᵥ F⌣F′) = (ρ *ᵇ) E ᶜ│ᵥ (ρ *ᶜᵇ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (E⌣E′ ➕₁ Q) = (ρ *ᶜᶜ⌣) E⌣E′ ➕₁ (ρ *) Q
   (ρ *ᶜᶜ⌣) (P │ᶜᶜ F⌣F′) = (ρ *) P │ᶜᶜ (ρ *ᶜᶜ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (E⌣E′ ᶜᶜ│ Q) = (ρ *ᶜᶜ⌣) E⌣E′ ᶜᶜ│ (ρ *) Q
   (ρ *ᶜᶜ⌣) (_│•_ {y = y} {z = z} {R = R} {R′} E⌣E′ F⌣F′) rewrite pop-comm ρ y R | pop-comm ρ z R′ =
      (ρ *ᵇᵇ⌣) E⌣E′ │• (ρ *ᶜᶜ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (_│•ᵥ_ {y = y} {R = R} E⌣E′ F⌣F′) rewrite pop-comm ρ y R = (ρ *ᵇᵇ⌣) E⌣E′ │•ᵥ (ρ *ᶜᵇ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (E⌣E′ │ᵥ F⌣F′) = (ρ *ᵇᵇ⌣) E⌣E′ │ᵥ (ρ *ᵇᵇ⌣) F⌣F′
   (ρ *ᶜᶜ⌣) (νᶜᶜ_ {a = a} {a′} {E} {E′} E⌣E′) with (suc ρ *ᶜ) E | (suc ρ *ᶜ) E′ | (suc ρ *ᶜᶜ⌣) E⌣E′
   ... | E† | E‡ | suc-ρ*E⌣E′ rewrite ᴿ+-comm 1 ρ a | ᴿ+-comm 1 ρ a′ = νᶜᶜ suc-ρ*E⌣E′
   (ρ *ᶜᶜ⌣) (! E⌣E′) = ! ((ρ *ᶜᶜ⌣) E⌣E′)
{-
   -- Residuation preserves concurrency.
   /-preserves-⌣ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → E′ ⌣₁[ a′⌣a″ ] E″ → (E⌣E″ : E ⌣₁[ a⌣a″ ] E″) →
          Delta′.E′/E (⊖₁ E⌣E′) ⌣₁[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ a⌣a″ ] Delta′.E′/E (⊖₁ E⌣E″)
   /-preserves-⌣ {E = x •∙ ._} E⌣E′ () E⌣E″
   /-preserves-⌣ {E = • x 〈 y 〉∙ ._} E⌣E′ () E⌣E″
   /-preserves-⌣ (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᵇ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᵇ│ᶜ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᵇ F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᶜ F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │•ᵇ F) (E⌣E″ │•ᵇ .F) with ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E″/E ᵀΔ _ | E′/E⌣E″/E = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │•ᵇ F) (E⌣E″ │•ᵇ .F) with ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E″/E ᵀΔ _ | E′/E⌣E″/E = E′/E⌣E″/E │•ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │•ᶜ F) (E⌣E″ │•ᵇ .F) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│• F′⌣F″) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│• F′⌣F″) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │ᵥᵇ F) (E⌣E″ │ᵥᵇ .F) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │ᵥᵇ F) (E⌣E″ │ᵥᵇ .F) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᵇ .F) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = E″/E ᵇ│ᵥ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = E″/E ᶜ│ᵥ (push *ᶜᵇ⌣) F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᵇ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᵇ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᵇ F) (P │ᵇᶜ F⌣F′) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ (push *ᵇᶜ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᶜ F) (P │ᶜᶜ F⌣F′) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ (push *ᶜᶜ⌣) F⌣F′
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᶜᶜ│ (push *) Q
   /-preserves-⌣ (E⌣E′ │•ᵇ F) (E′⌣E″ │• F⌣F′) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E⌣E′ │•ᵇ F) (E′⌣E″ │•ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E⌣E′ │ᵥᵇ F) (E′⌣E″ │ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │•ᶜ F) (E⌣E″ │•ᶜ .F) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│• F′⌣F″) (E⌣E″ │•ᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│• F⌣F′) (E⌣E″ │•ᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᶜ .F) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᶜ F
   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ F⌣F′) (E⌣E′ │ᵥᶜ F′) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᵇ│ᵥ F⌣F′
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ F⌣F′) (E⌣E′ │ᵥᶜ F′) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᵥ F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   /-preserves-⌣ (E ᶜ│ᵇ F) (P │ᵇᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ F′⌣F″
   /-preserves-⌣ (E ᶜ│ᶜ F) (P │ᶜᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = _ │ᶜᶜ F′⌣F″
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᶜᶜ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᶜᶜ│ Q
   /-preserves-⌣ (E⌣E′ │•ᶜ F) (E′⌣E″ │• F′⌣F″) (E⌣E″ │•ᶜ F′) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (E⌣E′ │•ᶜ F) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (E⌣E′ │ᵥᶜ F) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥ F′⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (E ᵇ│• F′⌣F″) (.E ᵇ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇ) E ᶜ│• F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (E ᵇ│• F′⌣F″) (.E ᵇ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇ) E ᵇ│• F′/F⌣F″/F
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᵇ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇ) E ᶜ│• F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (E ᵇ│ᵥ F′⌣F″) (.E ᵇ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (E ᵇ│ᵥ F′⌣F″) (.E ᵇ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (.E ᵇ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᵇᵇ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᵇᶜ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᵇᶜ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᶜᶜ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᶜᶜ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᵇᶜ F′/F⌣F″/F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᶜᶜ F′/F⌣F″/F
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *) P │ᶜᶜ F′/F⌣F″/F
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │• F′⌣F″) (E′ ᵇ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇᵇ⌣) E⌣E′ │• F′/F⌣F″/F
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │•ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇᵇ⌣) E⌣E′ │•ᵥ F′/F⌣F″/F
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │•ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = (push *ᵇᵇ⌣) E⌣E′ │• F′/F⌣F″/F
   /-preserves-⌣ (E ᵇ│ᵥ F⌣F′) (E⌣E′ │ᵥ F′⌣F″) (E′ ᵇ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᶜ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = _ ᶜ│• F′/F⌣F″/F
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (.E ᶜ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = E ᶜ│ᵥ F′/F⌣F″/F
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᶜᶜ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = P │ᶜᶜ F′/F⌣F″/F
   /-preserves-⌣ (E ᶜ│• F⌣F′) (E′⌣E″ │• F′⌣F″) (E′ ᶜ│• F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = E′⌣E″ │• F′/F⌣F″/F
   /-preserves-⌣ (E ᶜ│• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = E′⌣E″ │•ᵥ F′/F⌣F″/F
   /-preserves-⌣ (E ᶜ│ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = E′⌣E″ │ᵥ F′/F⌣F″/F
   /-preserves-⌣ (E⌣E′ │• F⌣F′) (E′⌣E″ │• F′⌣F″) (E⌣E″ │• F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = (pop _ *ᵇᵇ⌣) E′/E⌣E″/E │• F′/F⌣F″/F
   /-preserves-⌣ (E⌣E′ │• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = (pop _ *ᵇᵇ⌣) E′/E⌣E″/E │•ᵥ F′/F⌣F″/F
   /-preserves-⌣ (E⌣E′ │•ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = (pop _ *ᵇᵇ⌣) E′/E⌣E″/E │ᵥ F′/F⌣F″/F
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ (E′/E⌣E″/E │ᵥ F′/F⌣F″/F)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ {!!}
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ (E′/E⌣E″/E │•ᵥ F′/F⌣F″/F)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ (E′/E⌣E″/E │•ᵥ F′/F⌣F″/F)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = {!!}
   /-preserves-⌣ (ν• E⌣E′) (ν• E′⌣E″) (ν• E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν• E⌣E′) (ν•ᵇ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν• E⌣E′) (ν•ᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵇᵇ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵛᵛ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵇᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᶜ E⌣E′) (νᶜᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (νᵇᵇ_ {a = x •} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵇᵇ_ {a = • x} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵇᵇ E⌣E′) (νᵇᵇ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᵇ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ (swap *ᶜᶜ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = x •} E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵛᵛ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵛᵛ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ E⌣E′) (νᵛᵛ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᶜ ((swap *ᵇᶜ⌣) E′/E⌣E″/E)
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵛᵛ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ ((swap *ᶜᶜ⌣) E′/E⌣E″/E)
   /-preserves-⌣ (νᵇᵇ_ {a = x •} E⌣E′) (νᵇᶜ E′⌣E″) (νᵇᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵇᵇ_ {a = • x} E⌣E′) (νᵇᶜ E′⌣E″) (νᵇᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᶜ E′⌣E″) (νᵇᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵇᶜ E⌣E′) (νᶜᶜ E′⌣E″) (νᵇᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᶜᶜ E⌣E′) (νᶜᶜ E′⌣E″) (νᶜᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ E′/E⌣E″/E
   /-preserves-⌣ (! E⌣E′) (! E′⌣E″) (! E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E
-}
