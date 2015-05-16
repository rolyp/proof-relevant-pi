-- Residual of a renaming and an action. TODO: define ρ / a.
module Action.Ren where

   open import SharedModules

   open import Ext

   open import Action as ᴬ using (Actionᵇ; Actionᶜ; Action; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Name using (_+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable);
      open ᴿ.Renameable ⦃...⦄ renaming (
         _* to _*′; *-preserves-≃ₑ to *-preserves-≃ₑ′; *-preserves-∘ to *-preserves-∘′; *-preserves-id to *-preserves-id′
      )

   instance
      renᵇ : Renameable Actionᵇ
      renᵇ = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᵇ Γ → Actionᵇ Γ′
            (ρ *) (x •) = (ρ *′) x •
            (ρ *) (• x) = • (ρ *′) x

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ (x •) = cong _• (ρ≃ₑσ x)
            *-preserves-≃ₑ ρ≃ₑσ (• x) = cong •_ (ρ≃ₑσ x)

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ (x •) = refl
            *-preserves-∘ (• x) = refl

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Actionᵇ Γ}
            *-preserves-id (x •) = cong _• (*-preserves-id′ x)
            *-preserves-id (• x) = cong •_ (*-preserves-id′ x)

      renᶜ : Renameable Actionᶜ
      renᶜ = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Actionᶜ Γ → Actionᶜ Γ′
            (ρ *) • x 〈 y 〉 = • (ρ *′) x 〈 (ρ *′) y 〉
            (ρ *) τ = τ

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ • x 〈 y 〉 = cong₂ •_〈_〉 (ρ≃ₑσ x) (ρ≃ₑσ y)
            *-preserves-≃ₑ ρ≃ₑσ τ = refl

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ • x 〈 y 〉 = refl
            *-preserves-∘ τ = refl

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Actionᶜ Γ}
            *-preserves-id • x 〈 y 〉 = cong₂ •_〈_〉 (*-preserves-id′ x) (*-preserves-id′ y)
            *-preserves-id τ = refl

      ren : Renameable Action
      ren = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Action Γ → Action Γ′
            (ρ *) (a ᵇ) = (ρ *′) a ᵇ
            (ρ *) (a ᶜ) = (ρ *′) a ᶜ

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ (a ᵇ) = cong _ᵇ (*-preserves-≃ₑ′ ρ≃ₑσ a)
            *-preserves-≃ₑ ρ≃ₑσ (a ᶜ) = cong _ᶜ (*-preserves-≃ₑ′ ρ≃ₑσ a)

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ (a ᵇ) = cong _ᵇ (*-preserves-∘′ a)
            *-preserves-∘ (a ᶜ) = cong _ᶜ (*-preserves-∘′ a)

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Action Γ}
            *-preserves-id (a ᵇ) = cong _ᵇ (*-preserves-id′ a)
            *-preserves-id (a ᶜ) = cong _ᶜ (*-preserves-id′ a)

   -- More generally, (ρ / a) ∘ a ≡ ρ * (a / ρ), where ρ / a = ρ + inc a.
   ren-preserves-inc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → inc ≃ₑ inc ∘ ρ *′
   ren-preserves-inc _ (_ • ᵇ) = refl
   ren-preserves-inc _ ((• _) ᵇ) = refl
   ren-preserves-inc _ (• _ 〈 _ 〉 ᶜ) = refl
   ren-preserves-inc _ (τ ᶜ) = refl

   ren-preserves-target : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → (_+_ Γ′) ∘ inc ≃ₑ (_+_ Γ′) ∘ inc ∘ ρ *′
   ren-preserves-target {Γ′ = Γ′} ρ = cong (_+_ Γ′) ∘ ren-preserves-inc ρ
