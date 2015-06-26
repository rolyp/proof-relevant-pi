-- Extend residual of a renaming and an action to action sequences.
module Action.Seq2.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Action as ᴬ using (inc; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren using (ren-preserves-inc; ren-preserves-target)
   open import Action.Seq2 as ᴬ⋆ using (Action⋆; Action⋆↱; Action⋆↲; inc⋆); open ᴬ⋆.Action⋆
   open import Name using (_+_; +-assoc; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; suc; suc-preserves-≃ₑ; suc-preserves-id; suc-preserves-∘; _ᴿ+_);
      open ᴿ.Renameable ⦃...⦄ renaming (
         _* to _*′; *-preserves-≃ₑ to *-preserves-≃ₑ′; *-preserves-∘ to *-preserves-∘′; *-preserves-id to *-preserves-id′
      )

   _* : ∀ {Γ Γ′} → Ren Γ Γ′ → Action⋆ Γ → Action⋆ Γ′
   ren-preserves-inc⋆ : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ a⋆ → inc⋆ a⋆ ≡ inc⋆ ((ρ *) a⋆)

   (ρ *) [ a ] = [ (ρ *′) a ]
   (_ *) [] = []
   (ρ *) (a⋆ ⍮ a′⋆) = (ρ *) a⋆ ⍮ Action⋆↱ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆)

   ren-preserves-inc⋆ ρ [ a ] = ren-preserves-inc ρ a
   ren-preserves-inc⋆ ρ [] = refl
   ren-preserves-inc⋆ ρ (a⋆ ⍮ a′⋆) =
      let bib : ((ρ ᴿ+ inc⋆ a⋆) *) a′⋆ ≅ Action⋆↱ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆)
          bib = ≅-sym (Action⋆↲ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆))
          blah = ≅-to-≡ (
             begin
                inc⋆ a′⋆
             ≡⟨ ren-preserves-inc⋆ (ρ ᴿ+ inc⋆ a⋆) a′⋆ ⟩
                inc⋆ (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆)
             ≅⟨ ≅-cong✴ Action⋆ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) inc⋆ bib ⟩
                inc⋆ (Action⋆↱ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆))
             ∎) in
      cong₂ _+_ (ren-preserves-inc⋆ ρ a⋆) blah
      where open ≅-Reasoning

   instance
      ren : Renameable Action⋆
      ren = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            -- Easy induction, using functoriality of * and (ᴿ+ Γ).
            *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
            *-preserves-≃ₑ ρ≃ₑσ [] = refl
            *-preserves-≃ₑ ρ≃ₑσ _ = {!!}
--          *-preserves-≃ₑ ρ≃ₑσ (a ᵇ∷ a⋆) = cong₂ _ᵇ∷_ (*-preserves-≃ₑ′ ρ≃ₑσ a) (*-preserves-≃ₑ (suc-preserves-≃ₑ ρ≃ₑσ) a⋆)
--          *-preserves-≃ₑ ρ≃ₑσ (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-≃ₑ′ ρ≃ₑσ a) (*-preserves-≃ₑ ρ≃ₑσ a⋆)

            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ [] = refl
            *-preserves-∘ _ = {!!}
--          *-preserves-∘ {ρ = ρ} {σ} (a ᵇ∷ a⋆) =
--             cong₂ _ᵇ∷_ (*-preserves-∘′ a) (trans (*-preserves-∘ a⋆) (*-preserves-≃ₑ (suc-preserves-∘ ρ σ) a⋆))
--          *-preserves-∘ (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-∘′ a) (*-preserves-∘ a⋆)

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Action⋆ Γ}
            *-preserves-id [] = refl
            *-preserves-id _ = {!!}
--          *-preserves-id (a ᵇ∷ a⋆) =
--             cong₂ _ᵇ∷_ (*-preserves-id′ a) (trans (*-preserves-≃ₑ suc-preserves-id a⋆) (*-preserves-id a⋆))
--          *-preserves-id (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-id′ a) (*-preserves-id a⋆)

{-
   ren-preserves-inc⋆-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ Δ′ (a⋆ : Action⋆ (Γ + Δ′)) →
                              Γ + (Δ′ + inc⋆ a⋆) ≡ Γ + Δ′ + inc⋆ (((ρ ᴿ+ Δ′) *′) a⋆)
   ren-preserves-inc⋆-assoc {Γ} ρ Δ′ a⋆ =
      trans (sym (+-assoc Γ Δ′ (inc⋆ a⋆))) (cong (_+_ (Γ + Δ′)) (ren-preserves-inc⋆ (ρ ᴿ+ Δ′) a⋆))
-}
