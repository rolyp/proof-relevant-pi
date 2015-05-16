-- Residual of a renaming and an action sequence.
module Action.Seq.Ren where

   open import SharedModules

   open import Ext

   open import Action using (inc)
   open import Action.Ren using (ren-preserves-target)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Name using (_+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; _ᴿ+_);
      open ᴿ.Renameable ⦃...⦄ renaming (
         _* to _*′; *-preserves-≃ₑ to *-preserves-≃ₑ′; *-preserves-∘ to *-preserves-∘′; *-preserves-id to *-preserves-id′
      )

   instance
      ren : Renameable Action⋆
      ren = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Action⋆ Γ → Action⋆ Γ′
            _* _ [] = []
            _* ρ (a ∷ a⋆) = (ρ *′) a ∷ subst Action⋆ (ren-preserves-target ρ a) (((ρ ᴿ+ inc a) *) a⋆)

            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ a∗ = {!!}

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ a∗ = {!!}

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Action⋆ Γ}
            *-preserves-id a⋆ = {!!}
