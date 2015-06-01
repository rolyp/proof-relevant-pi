-- Concurrent transitions are closed under renamings.
module Transition.Concur.Ren where

   open import SharedModules

   open import Action as ᴬ using (Action; _ᴬ⌣_); open ᴬ._ᴬ⌣_; open ᴬ.Action; open ᴬ.Actionᵇ
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; suc); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (ᴬ⊖; Concur₁; module Concur₁); open Concur₁
   open import Transition.Ren

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

   (ρ *ᵇᵇ⌣) (_ᵇ│ᵇ_ {P = P} {Q} E F) rewrite ᴿ+-comm 1 ρ P | ᴿ+-comm 1 ρ Q = (ρ *ᵇ) E ᵇ│ᵇ (ρ *ᵇ) F
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

   (ρ *ᶜᵇ⌣) (_ᶜ│ᵇ_ {P = P} E F) rewrite ᴿ+-comm 1 ρ P = (ρ *ᶜ) E ᶜ│ᵇ (ρ *ᵇ) F
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
