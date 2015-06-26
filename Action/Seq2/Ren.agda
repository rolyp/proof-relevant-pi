-- Extend residual of a renaming and an action to action sequences. Mainly an exercise in heterogeneous
-- equality, using functoriality of * and (ᴿ+ Γ).
module Action.Seq2.Ren where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open import Action as ᴬ using (inc; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren using (ren-preserves-inc; ren-preserves-target)
   open import Action.Seq2 as ᴬ⋆ using (Action⋆; Action⋆↱; Action⋆↲; inc⋆); open ᴬ⋆.Action⋆
   open import Name using (_+_; +-assoc; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; _ᴿ+_; +-preserves-≃ₑ; +-preserves-id; +-preserves-∘);
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
   ren-preserves-inc⋆ {Γ′ = Γ′} ρ (a⋆ ⍮ a′⋆) =
      let IHₗ = ren-preserves-inc⋆ ρ a⋆
          IHᵣ = let open ≅-Reasoning in
             begin
                inc⋆ a′⋆
             ≡⟨ ren-preserves-inc⋆ (ρ ᴿ+ inc⋆ a⋆) a′⋆ ⟩
                inc⋆ (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆)
             ≅⟨ ≅-cong✴ Action⋆ (cong (_+_ Γ′) IHₗ) inc⋆ (≅-sym (Action⋆↲ (cong (_+_ Γ′) IHₗ) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆))) ⟩
                inc⋆ (Action⋆↱ (cong (_+_ Γ′) IHₗ) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆))
             ∎ in
      cong₂ _+_ IHₗ (≅-to-≡ IHᵣ)

   *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
   *-preserves-≃ₑ ρ≃ₑσ [ a ] = cong [_] (*-preserves-≃ₑ′ ρ≃ₑσ a)
   *-preserves-≃ₑ _ [] = refl
   *-preserves-≃ₑ {ρ = ρ} {σ} ρ≃ₑσ (a⋆ ⍮ a′⋆) = ≅-to-≡ (≅-cong₂ _⍮_ (≡-to-≅ (*-preserves-≃ₑ ρ≃ₑσ a⋆)) (
      let open ≅-Reasoning in
      begin
         subst Action⋆ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) (((ρ ᴿ+ inc⋆ a⋆) *) a′⋆)
      ≅⟨ Action⋆↲ (cong (_+_ _) (ren-preserves-inc⋆ ρ a⋆)) _ ⟩
         ((ρ ᴿ+ inc⋆ a⋆) *) a′⋆
      ≅⟨ ≡-to-≅ (*-preserves-≃ₑ (+-preserves-≃ₑ (inc⋆ a⋆) ρ≃ₑσ) a′⋆) ⟩
         ((σ ᴿ+ inc⋆ a⋆) *) a′⋆
      ≅⟨ ≅-sym (Action⋆↲ (cong (_+_ _) (ren-preserves-inc⋆ σ a⋆)) _) ⟩
         subst Action⋆ (cong (_+_ _) (ren-preserves-inc⋆ σ a⋆)) (((σ ᴿ+ inc⋆ a⋆) *) a′⋆)
      ∎))

   instance
      ren : Renameable Action⋆
      ren = record {
            _* = _*;
            *-preserves-≃ₑ = *-preserves-≃ₑ;
            *-preserves-∘ = *-preserves-∘;
            *-preserves-id = *-preserves-id
         }
         where
            *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *
            *-preserves-∘ [] = refl
            *-preserves-∘ _ = {!!}
--          *-preserves-∘ {ρ = ρ} {σ} (a ᵇ∷ a⋆) =
--             cong₂ _ᵇ∷_ (*-preserves-∘′ a) (trans (*-preserves-∘ a⋆) (*-preserves-≃ₑ (suc-preserves-∘ ρ σ) a⋆))
--          *-preserves-∘ (a ᶜ∷ a⋆) = cong₂ _ᶜ∷_ (*-preserves-∘′ a) (*-preserves-∘ a⋆)

            *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = Action⋆ Γ}
            *-preserves-id [ a ] = cong [_] (*-preserves-id′ a)
            *-preserves-id [] = refl
            *-preserves-id (a⋆ ⍮ a′⋆) = ≅-to-≡ (
                  ≅-cong₂ _⍮_ (≡-to-≅ (*-preserves-id a⋆)) (
                     let open ≅-Reasoning in
                     begin
                        subst Action⋆ (cong (_+_ _) (ren-preserves-inc⋆ id a⋆)) (((id ᴿ+ inc⋆ a⋆) *) a′⋆)
                     ≅⟨ {!!} ⟩
                        a′⋆
                     ∎)
               )
--             (trans (*-preserves-≃ₑ suc-preserves-id a⋆) (*-preserves-id a⋆))

{-
   ren-preserves-inc⋆-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ Δ′ (a⋆ : Action⋆ (Γ + Δ′)) →
                              Γ + (Δ′ + inc⋆ a⋆) ≡ Γ + Δ′ + inc⋆ (((ρ ᴿ+ Δ′) *′) a⋆)
   ren-preserves-inc⋆-assoc {Γ} ρ Δ′ a⋆ =
      trans (sym (+-assoc Γ Δ′ (inc⋆ a⋆))) (cong (_+_ (Γ + Δ′)) (ren-preserves-inc⋆ (ρ ᴿ+ Δ′) a⋆))
-}
