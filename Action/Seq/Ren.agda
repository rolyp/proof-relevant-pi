-- Extend residual of a renaming and an action to action sequences.
module Action.Seq.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Action as ᴬ using (inc; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren using (ren-preserves-target)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Name using (_+_; +-assoc; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; suc; +-preserves-≃ₑ; +-preserves-id; +-preserves-∘; _ᴿ+_);
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
            (_ *) [] = []
            (ρ *) (a ᵇ∷ a⋆) = (ρ *′) a ᵇ∷ ((ρ ᴿ+ 1) *) a⋆
            (ρ *) (a ᶜ∷ a⋆) = (ρ *′) a ᶜ∷ (ρ *) a⋆

            -- Easy induction, using functoriality of * and suc.
            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ [] = refl
            *-preserves-≃ₑ ρ≃ₑσ (a ᵇ∷ a⋆) = cong₂ _ᵇ∷_ (*-preserves-≃ₑ′ ρ≃ₑσ a) (*-preserves-≃ₑ (+-preserves-≃ₑ 1 ρ≃ₑσ) a⋆)
            *-preserves-≃ₑ ρ≃ₑσ (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-≃ₑ′ ρ≃ₑσ a) (*-preserves-≃ₑ ρ≃ₑσ a⋆)

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ [] = refl
            *-preserves-∘ {ρ = ρ} {σ} (a ᵇ∷ a⋆) =
               cong₂ _ᵇ∷_ (*-preserves-∘′ a) (trans (*-preserves-∘ a⋆) (*-preserves-≃ₑ (+-preserves-∘ 1 ρ σ) a⋆))
            *-preserves-∘ (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-∘′ a) (*-preserves-∘ a⋆)

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Action⋆ Γ}
            *-preserves-id [] = refl
            *-preserves-id (a ᵇ∷ a⋆) =
               cong₂ _ᵇ∷_ (*-preserves-id′ a) (trans (*-preserves-≃ₑ (+-preserves-id 1) a⋆) (*-preserves-id a⋆))
            *-preserves-id (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-id′ a) (*-preserves-id a⋆)

   ren-preserves-inc⋆ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → inc⋆ ≃ₑ inc⋆ ∘ ρ *′
   ren-preserves-inc⋆ ρ [] = refl
   ren-preserves-inc⋆ ρ (a ᵇ∷ a⋆) rewrite ren-preserves-inc⋆ (suc ρ) a⋆ = refl
   ren-preserves-inc⋆ ρ (a ᶜ∷ a⋆) rewrite ren-preserves-inc⋆ ρ a⋆ = refl

   ren-preserves-inc⋆-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ Δ′ (a⋆ : Action⋆ (Γ + Δ′)) →
                              Γ + (Δ′ + inc⋆ a⋆) ≡ Γ + Δ′ + inc⋆ (((ρ ᴿ+ Δ′) *′) a⋆)
   ren-preserves-inc⋆-assoc {Γ} ρ Δ′ a⋆ =
      trans (sym (+-assoc Γ Δ′ (inc⋆ a⋆))) (cong (_+_ (Γ + Δ′)) (ren-preserves-inc⋆ (ρ ᴿ+ Δ′) a⋆))
