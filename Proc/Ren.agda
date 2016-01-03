-- Apply a renaming to a process.
module Proc.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (
         Ren; suc; push; pop; swap; +-preserves-≃ₑ; +-preserves-id; +-preserves-∘; Renameable; module Renameable; ᴺren
      );
      open Renameable ⦃...⦄ renaming (
         _* to _*′; *-preserves-≃ₑ to *-preserves-≃ₑ′; *-preserves-∘ to *-preserves-∘′; *-preserves-id to *-preserves-id′
      )

   instance
      ren : Renameable Proc
      ren = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Proc Γ → Proc Γ′
            (ρ *) Ο = Ο
            (ρ *) (x •∙ P) = (ρ *′) x •∙ (suc ρ *) P
            (ρ *) (• x 〈 y 〉∙ P) = • (ρ *′) x 〈 (ρ *′) y 〉∙ (ρ *) P
            (ρ *) (P ➕ Q) = (ρ *) P ➕ (ρ *) Q
            (ρ *) (P │ Q) = (ρ *) P │ (ρ *) Q
            (ρ *) (ν P) = ν (suc ρ *) P
            (ρ *) (! P) = ! (ρ *) P

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ Ο = refl
            *-preserves-≃ₑ ρ≃ₑσ (x •∙ P) = cong₂ _•∙_ (ρ≃ₑσ x) (*-preserves-≃ₑ (+-preserves-≃ₑ 1 ρ≃ₑσ) P)
            *-preserves-≃ₑ ρ≃ₑσ (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (ρ≃ₑσ x) (ρ≃ₑσ y) (*-preserves-≃ₑ ρ≃ₑσ P)
            *-preserves-≃ₑ ρ≃ₑσ (P ➕ Q) = cong₂ _➕_ (*-preserves-≃ₑ ρ≃ₑσ P) (*-preserves-≃ₑ ρ≃ₑσ Q)
            *-preserves-≃ₑ ρ≃ₑσ (P │ Q) = cong₂ _│_ (*-preserves-≃ₑ ρ≃ₑσ P) (*-preserves-≃ₑ ρ≃ₑσ Q)
            *-preserves-≃ₑ ρ≃ₑσ (ν P) = cong ν_ (*-preserves-≃ₑ (+-preserves-≃ₑ 1 ρ≃ₑσ) P)
            *-preserves-≃ₑ ρ≃ₑσ (! P) = cong !_ (*-preserves-≃ₑ ρ≃ₑσ P)

            -- TODO: try again to move this to the typeclass?
            suc-∘-* : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → (suc ρ ∘ suc σ) * ≃ₑ suc (ρ ∘ σ) *
            suc-∘-* = *-preserves-≃ₑ (+-preserves-∘ 1 _ _)

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ Ο = refl
            *-preserves-∘ (x •∙ P) = cong₂ _•∙_ refl (trans (*-preserves-∘ P) (suc-∘-* P))
            *-preserves-∘ (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ refl refl (*-preserves-∘ P)
            *-preserves-∘ (P ➕ Q) = (*-preserves-∘ P) ⟨ cong₂ _➕_ ⟩ (*-preserves-∘ Q)
            *-preserves-∘ (P │ Q) = (*-preserves-∘ P) ⟨ cong₂ _│_ ⟩ (*-preserves-∘ Q)
            *-preserves-∘ (ν P) = cong ν_ (trans (*-preserves-∘ P) (suc-∘-* P))
            *-preserves-∘ (! P) = cong !_ (*-preserves-∘ P)

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Proc Γ}
            *-preserves-id Ο = refl
            *-preserves-id (x •∙ P) =
               *-preserves-id′ x ⟨ cong₂ _•∙_ ⟩ trans (*-preserves-≃ₑ (+-preserves-id 1) P) (*-preserves-id P)
            *-preserves-id (• x 〈 y 〉∙ P) = cong₃ •_〈_〉∙_ (*-preserves-id′ x) (*-preserves-id′ y) (*-preserves-id P)
            *-preserves-id (P ➕ Q) = *-preserves-id P ⟨ cong₂ _➕_ ⟩ *-preserves-id Q
            *-preserves-id (P │ Q) = *-preserves-id P ⟨ cong₂ _│_ ⟩ *-preserves-id Q
            *-preserves-id (ν P) = cong ν_ (trans (*-preserves-≃ₑ (+-preserves-id 1) P) (*-preserves-id P))
            *-preserves-id (! P) = cong !_ (*-preserves-id P)
