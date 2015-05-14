-- Apply a renaming to a process.
module Proc.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (
         Ren; suc; push; pop; swap; suc-preserves-≃ₑ; suc-preserves-id; suc-preserves-∘; Renameable; module Renameable; ᴺren
      );
      open Renameable ⦃...⦄ renaming (
         _*_ to _*′_; *-preserves-≃ₑ to *-preserves-≃ₑ′; ∘-*-factor to ∘-*-factor′; id-* to id-*′
      )

   instance
      ren : Renameable Proc
      ren = record { _*_ = _*_; *-preserves-≃ₑ = *-preserves-≃ₑ; ∘-*-factor = ∘-*-factor; id-* = id-* }
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

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → (_*_ ρ) ≃ₑ (_*_ σ)
            *-preserves-≃ₑ ρ≃ₑσ Ο = refl
            *-preserves-≃ₑ ρ≃ₑσ (x •∙ P) = cong₂ _•∙_ (ρ≃ₑσ x) (*-preserves-≃ₑ (suc-preserves-≃ₑ ρ≃ₑσ) P)
            *-preserves-≃ₑ ρ≃ₑσ (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (ρ≃ₑσ x) (ρ≃ₑσ y) (*-preserves-≃ₑ ρ≃ₑσ P)
            *-preserves-≃ₑ ρ≃ₑσ (P ➕ Q) = cong₂ _➕_ (*-preserves-≃ₑ ρ≃ₑσ P) (*-preserves-≃ₑ ρ≃ₑσ Q)
            *-preserves-≃ₑ ρ≃ₑσ (P │ Q) = cong₂ _│_ (*-preserves-≃ₑ ρ≃ₑσ P) (*-preserves-≃ₑ ρ≃ₑσ Q)
            *-preserves-≃ₑ ρ≃ₑσ (ν P) = cong ν_ (*-preserves-≃ₑ (suc-preserves-≃ₑ ρ≃ₑσ) P)
            *-preserves-≃ₑ ρ≃ₑσ (! P) = cong !_ (*-preserves-≃ₑ ρ≃ₑσ P)

            -- TODO: try again to move this to the typeclass?
            suc-∘-* : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → _*_ (suc ρ ∘ suc σ) ≃ₑ _*_ (suc (ρ ∘ σ))
            suc-∘-* = *-preserves-≃ₑ (suc-preserves-∘ _ _)

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (P : Proc Γ₁) → ρ * σ * P ≡ (ρ ∘ σ) * P
            ∘-*-factor Ο = refl
            ∘-*-factor (x •∙ P) = cong₂ _•∙_ refl (trans (∘-*-factor P) (suc-∘-* P))
            ∘-*-factor (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ refl refl (∘-*-factor P)
            ∘-*-factor (P ➕ Q) = (∘-*-factor P) ⟨ cong₂ _➕_ ⟩ (∘-*-factor Q)
            ∘-*-factor (P │ Q) = (∘-*-factor P) ⟨ cong₂ _│_ ⟩ (∘-*-factor Q)
            ∘-*-factor (ν P) = cong ν_ (trans (∘-*-factor P) (suc-∘-* P))
            ∘-*-factor (! P) = cong !_ (∘-*-factor P)

            id-* : ∀ {Γ} (P : Proc Γ) → id * P ≡ P
            id-* Ο = refl
            id-* (x •∙ P) = id-*′ x ⟨ cong₂ _•∙_ ⟩ trans (*-preserves-≃ₑ suc-preserves-id P) (id-* P)
            id-* (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (id-*′ x) (id-*′ y) (id-* P)
            id-* (P ➕ Q) = id-* P ⟨ cong₂ _➕_ ⟩ id-* Q
            id-* (P │ Q) = id-* P ⟨ cong₂ _│_ ⟩ id-* Q
            id-* (ν P) = cong ν_ (trans (*-preserves-≃ₑ suc-preserves-id P) (id-* P))
            id-* (! P) = cong !_ (id-* P)
