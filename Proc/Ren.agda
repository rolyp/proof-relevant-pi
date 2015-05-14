-- Apply a renaming to a process.
module Proc.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (
         Ren; _∘_; ∘-assoc; suc; push; pop; swap; suc-preserves-∘; Renameable; module Renameable; ᴺren
      );
      open Renameable ⦃...⦄ renaming (_*_ to _*′_; ∘-*-factor to ∘-*-factor′; id-* to id-*′)

   instance
      ren : Renameable Proc
      ren = record { _*_ = _*_; ∘-*-factor = ∘-*-factor; id-* = id-* }
         where
            infixr 8 _*_
            _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Proc Γ → Proc Γ′
            ρ * Ο = Ο
            ρ * (x •∙ P) = (ρ *′ x) •∙ (suc ρ * P)
            ρ * (• x 〈 y 〉∙ P) = • ρ *′ x 〈 ρ *′ y 〉∙ (ρ * P)
            ρ * (P ➕ Q) = ρ * P ➕ ρ * Q
            ρ * (P │ Q) = ρ * P │ ρ * Q
            ρ * (ν P) = ν (suc ρ * P)
            ρ * (! P) = ! (ρ * P)

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (P : Proc Γ₁) → ρ * σ * P ≡ (ρ ∘ σ) * P
            ∘-*-factor Ο = refl
            ∘-*-factor {ρ = ρ} {σ} (x •∙ P) rewrite ∘-*-factor {ρ = suc ρ} {suc σ} P | suc-preserves-∘ ρ σ =
               ∘-*-factor′ x ⟨ cong₂ _•∙_ ⟩ refl
            ∘-*-factor (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (∘-*-factor′ x) (∘-*-factor′ y) (∘-*-factor P)
            ∘-*-factor (P ➕ Q) = (∘-*-factor P) ⟨ cong₂ _➕_ ⟩ (∘-*-factor Q)
            ∘-*-factor (P │ Q) = (∘-*-factor P) ⟨ cong₂ _│_ ⟩ (∘-*-factor Q)
            ∘-*-factor {ρ = ρ} {σ} (ν P) rewrite ∘-*-factor {ρ = suc ρ} {suc σ} P | suc-preserves-∘ ρ σ = refl
            ∘-*-factor (! P) = cong !_ (∘-*-factor P)

            id-* : ∀ {Γ} (P : Proc Γ) → ᴿ.id * P ≡ P
            id-* Ο = refl
            id-* (x •∙ P) = id-*′ x ⟨ cong₂ _•∙_ ⟩ id-* P
            id-* (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (id-*′ x) (id-*′ y) (id-* P)
            id-* (P ➕ Q) = id-* P ⟨ cong₂ _➕_ ⟩ id-* Q
            id-* (P │ Q) = id-* P ⟨ cong₂ _│_ ⟩ id-* Q
            id-* (ν P) = cong ν_ (id-* P)
            id-* (! P) = cong !_ (id-* P)
