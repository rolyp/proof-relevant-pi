-- Apply a renaming to an action or action sequence.
module Action.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Actionᵇ; Actionᶜ; Action; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Name using (_+_)
   open import Ren as ᴿ using (Ren; _∘_; suc; suc-preserves-∘; id; pop; push; swap; Renameable);
      open ᴿ.Renameable ⦃...⦄ renaming (_*_ to _*′_; ∘-*-factor to ∘-*-factor′; id-* to id-*′)

   instance
      renᵇ : Renameable Actionᵇ
      renᵇ = record { _*_ = _*_; ∘-*-factor = ∘-*-factor; id-* = id-* }
         where
            infixr 8 _*_
            _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᵇ Γ → Actionᵇ Γ′
            ρ * (x •) = (ρ *′ x) •
            ρ * (• x) = • (ρ *′ x)

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (a : Actionᵇ Γ₁) → ρ * (σ * a) ≡ (ρ ∘ σ) * a
            ∘-*-factor (x •) = cong _• (∘-*-factor′ x)
            ∘-*-factor (• x) = cong •_ (∘-*-factor′ x)

            id-* : ∀ {Γ} (a : Actionᵇ Γ) → id * a ≡ a
            id-* (x •) = cong _• (id-*′ x)
            id-* (• x) = cong •_ (id-*′ x)

      renᶜ : Renameable Actionᶜ
      renᶜ = record { _*_ = _*_; ∘-*-factor = ∘-*-factor; id-* = id-* }
         where
            infixr 8 _*_
            _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᶜ Γ → Actionᶜ Γ′
            ρ * • x 〈 y 〉 = • ρ *′ x 〈 ρ *′ y 〉
            ρ * τ = τ

            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (a : Actionᶜ Γ₁) → ρ * (σ * a) ≡ (ρ ∘ σ) * a
            ∘-*-factor • x 〈 y 〉 = cong₂ •_〈_〉 (∘-*-factor′ x) (∘-*-factor′ y)
            ∘-*-factor τ = refl

            id-* : ∀ {Γ} (a : Actionᶜ Γ) → id * a ≡ a
            id-* • x 〈 y 〉 = cong₂ •_〈_〉 (id-*′ x) (id-*′ y)
            id-* τ = refl
