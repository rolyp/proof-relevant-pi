-- Apply a renaming to an action.
module Action.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Action as ᴬ using (Actionᵇ; Actionᶜ; Action; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Name using (_+_)
   open import Ren as ᴿ using (Ren; suc; suc-preserves-∘; pop; push; swap; Renameable);
      open ᴿ.Renameable ⦃...⦄ renaming (_*_ to _*′_; *-preserves-≃ₑ to *-preserves-≃ₑ′; ∘-*-factor to ∘-*-factor′; id-* to id-*′)

   instance
      renᵇ : Renameable Actionᵇ
      renᵇ = record { _*_ = _*_; *-preserves-≃ₑ = *-preserves-≃ₑ; ∘-*-factor = ∘-*-factor; id-* = id-* }
         where
            infixr 8 _*_
            _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᵇ Γ → Actionᵇ Γ′
            ρ * (x •) = (ρ *′ x) •
            ρ * (• x) = • (ρ *′ x)

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → (_*_ ρ) ≃ₑ (_*_ σ)
            *-preserves-≃ₑ ρ≃ₑσ (x •) = cong _• (ρ≃ₑσ x)
            *-preserves-≃ₑ ρ≃ₑσ (• x) = cong •_ (ρ≃ₑσ x)

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (a : Actionᵇ Γ₁) → ρ * (σ * a) ≡ (ρ ∘ σ) * a
            ∘-*-factor (x •) = refl
            ∘-*-factor (• x) = refl

            id-* : ∀ {Γ} (a : Actionᵇ Γ) → id * a ≡ a
            id-* (x •) = cong _• (id-*′ x)
            id-* (• x) = cong •_ (id-*′ x)

      renᶜ : Renameable Actionᶜ
      renᶜ = record { _*_ = _*_; *-preserves-≃ₑ = *-preserves-≃ₑ; ∘-*-factor = ∘-*-factor; id-* = id-* }
         where
            infixr 8 _*_
            _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᶜ Γ → Actionᶜ Γ′
            ρ * • x 〈 y 〉 = • ρ *′ x 〈 ρ *′ y 〉
            ρ * τ = τ

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → (_*_ ρ) ≃ₑ (_*_ σ)
            *-preserves-≃ₑ ρ≃ₑσ • x 〈 y 〉 = cong₂ •_〈_〉 (ρ≃ₑσ x) (ρ≃ₑσ y)
            *-preserves-≃ₑ ρ≃ₑσ τ = refl

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (a : Actionᶜ Γ₁) → ρ * (σ * a) ≡ (ρ ∘ σ) * a
            ∘-*-factor • x 〈 y 〉 = refl
            ∘-*-factor τ = refl

            id-* : ∀ {Γ} (a : Actionᶜ Γ) → id * a ≡ a
            id-* • x 〈 y 〉 = cong₂ •_〈_〉 (id-*′ x) (id-*′ y)
            id-* τ = refl
