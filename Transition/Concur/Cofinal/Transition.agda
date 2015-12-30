-- Symmetric residual of a transition and a cofinality witness.
module Transition.Concur.Cofinal.Transition where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_
   open import Action.Ren using (ren-preserves-inc; ren-preserves-target)
   open import Braiding.Proc using (_⋉_)
   open import Braiding.Transition using (_Δ_; ⊖)
   open import Name as ᴺ using (Cxt; _+_; +-assoc)
   open import Ren as ᴿ using (Renameable; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (﹙_,_,_,_﹚)
   open import Transition.Ren using (_*′)

   -- TODO: needs a better name; this is the image of an action in a braid.
   braid : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Δ′ → let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) in
           {A : Cxt → Set} ⦃ _ : Renameable A ⦄ (a : A (Γ′ + Δ′)) → A (Γ′ + Δ′)
   braid ˣ∇ˣ _ = id
   braid ᵇ∇ᵇ Δ′ = (swap ᴿ+ Δ′) *
   braid ᵇ∇ᶜ _ = id
   braid ᶜ∇ᵇ _ = id
   braid ᶜ∇ᶜ _ = id
   braid ᵛ∇ᵛ _ = id

   braid-preserves-inc : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in
                        inc ≃ₑ inc ∘ braid 𝑎 Δ′
   braid-preserves-inc ˣ∇ˣ _ _ = refl
   braid-preserves-inc ᵇ∇ᵇ Δ′ = ren-preserves-inc (swap ᴿ+ Δ′)
   braid-preserves-inc ᵇ∇ᶜ _ _ = refl
   braid-preserves-inc ᶜ∇ᵇ _ _ = refl
   braid-preserves-inc ᶜ∇ᶜ _ _ = refl
   braid-preserves-inc ᵛ∇ᵛ _ _ = refl

   braid-preserves-inc-assoc : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Δ′ → let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) in
                              (a : Action (Γ′ + Δ′)) → Γ′ + (Δ′ + inc a) ≡  Γ′ + Δ′ + inc (braid 𝑎 Δ′ a)
   braid-preserves-inc-assoc {Γ} {a₀} 𝑎 Δ′ a =
      let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)); open EqReasoning (setoid _) in
      begin
         Γ′ + (Δ′ + inc a)
      ≡⟨ sym (+-assoc Γ′ Δ′ (inc a)) ⟩
         Γ′ + Δ′ + inc a
      ≡⟨ cong (_+_ (Γ′ + Δ′)) (braid-preserves-inc 𝑎 Δ′ a) ⟩
         Γ′ + Δ′ + inc (braid 𝑎 Δ′ a)
      ∎

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ} {a₀ a₀′ : Action Γ} {𝑎 : a₀ ᴬ⌣ a₀′} {Γ′} {P P′ : Proc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) + Γ′)} {a R}
          (E : P —[ a - ι ]→ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Γ′ ﹚ P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc _
         γ/E : ﹙ _⋉_ , Γ , 𝑎 , Γ′ + inc a ﹚ (Proc↱ (+-assoc _ Γ′ (inc a)) R) R′
         E/γ : P′ —[ braid 𝑎 Γ′ a - ι ]→ Proc↱ (braid-preserves-inc-assoc 𝑎 Γ′ a) R′

   -- Heterogeneity juggling in the ᵇ∇ᵇ case.
   ⊖′[_,_] : ∀ {ι Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Γ′ {P P′ : Proc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) + Γ′)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Γ′ ﹚ P P′) → _Δ′_ {𝑎 = 𝑎} E γ
   ⊖′[ ˣ∇ˣ , Γ′ ] {a = _ ᵇ} E refl = refl Δ E
   ⊖′[ ˣ∇ˣ , Γ′ ] {a = _ ᶜ} E refl = refl Δ E
   ⊖′[_,_] {a₀ = a₀ ᵇ} {a₀′ ᵇ} ᵇ∇ᵇ Γ′ {P = P} {a = a ᵇ} {R} E refl =
      refl Δ subst (λ R → ((swap ᴿ+ Γ′) *) P —[ ((swap ᴿ+ Γ′) *) a ᵇ - _ ]→ R) (≅-to-≡ (
         ≅-trans (Proc↲ (ren-preserves-target (swap ᴿ+ Γ′) (a ᵇ)) (((swap ᴿ+ (Γ′ + 1)) *) R))
                 (≅-sym (Proc↲ (braid-preserves-inc-assoc (ᵇ∇ᵇ {a = a₀} {a₀′}) Γ′ (a ᵇ)) (((swap ᴿ+ (Γ′ + 1)) *) R)))
      )) (((swap ᴿ+ Γ′) *′) E)
   ⊖′[_,_] {a₀ = a₀ ᵇ} {a₀′ ᵇ} ᵇ∇ᵇ Γ′ {P = P} {a = a ᶜ} {R} E refl =
      refl Δ subst (λ R → ((swap ᴿ+ Γ′) *) P —[ ((swap ᴿ+ Γ′) *) a ᶜ - _ ]→ R) (≅-to-≡ (
         ≅-trans (Proc↲ (ren-preserves-target (swap ᴿ+ Γ′) (a ᶜ)) (((swap ᴿ+ Γ′) *) R))
                 (≅-sym (Proc↲ (braid-preserves-inc-assoc (ᵇ∇ᵇ {a = a₀} {a₀′}) Γ′ (a ᶜ)) _))
      )) (((swap ᴿ+ Γ′) *′) E)
   ⊖′[ ᵇ∇ᶜ , _ ] {a = _ ᵇ} E refl = refl Δ E
   ⊖′[ ᵇ∇ᶜ , _ ] {a = _ ᶜ} E refl = refl Δ E
   ⊖′[ ᶜ∇ᵇ , _ ] {a = _ ᵇ} E refl = refl Δ E
   ⊖′[ ᶜ∇ᵇ , _ ] {a = _ ᶜ} E refl = refl Δ E
   ⊖′[ ᶜ∇ᶜ , _ ] {a = _ ᵇ} E refl = refl Δ E
   ⊖′[ ᶜ∇ᶜ , _ ] {a = _ ᶜ} E refl = refl Δ E
   ⊖′[ ᵛ∇ᵛ , _ ] {a = _ ᵇ} E φ = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ E/φ
   ⊖′[ ᵛ∇ᵛ , _ ] {a = _ ᶜ} E φ = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ E/φ
