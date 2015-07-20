module Transition.Concur.Cofinal.Transition where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_
   open import Action.Ren using (ren-preserves-inc; ren-preserves-target)
   open import Braiding.Proc using (⋈-to-⋉)
   open import Braiding.Transition using (_Δ_; ⊖)
   open import Name as ᴺ using (_+_; +-assoc)
   open import Ren as ᴿ using (swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (⋈[_,_,_])
   open import Transition.Ren using (_*′)

   -- TODO: sort naming.
   blah : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Δ′ → let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) in
          (a : Action (Γ′ + Δ′)) → Action (Γ′ + Δ′)
   blah ˣ∇ˣ _ = id
   blah ᵇ∇ᵇ Δ′ = (swap ᴿ+ Δ′) *
   blah ᵇ∇ᶜ _ = id
   blah ᶜ∇ᵇ _ = id
   blah ᶜ∇ᶜ _ = id
   blah ᵛ∇ᵛ _ = id

   blah-preserves-inc : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in
                        inc ≃ₑ inc ∘ blah 𝑎 Δ′
   blah-preserves-inc ˣ∇ˣ _ _ = refl
   blah-preserves-inc ᵇ∇ᵇ Δ′ = ren-preserves-inc (swap ᴿ+ Δ′)
   blah-preserves-inc ᵇ∇ᶜ _ _ = refl
   blah-preserves-inc ᶜ∇ᵇ _ _ = refl
   blah-preserves-inc ᶜ∇ᶜ _ _ = refl
   blah-preserves-inc ᵛ∇ᵛ _ _ = refl

   blah-preserves-inc-assoc : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Δ′ → let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) in
                              (a : Action (Γ′ + Δ′)) → Γ′ + (Δ′ + inc a) ≡  Γ′ + Δ′ + inc (blah 𝑎 Δ′ a)
   blah-preserves-inc-assoc {Γ} {a₀} 𝑎 Δ′ a =
      let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)); open EqReasoning (setoid _) in
      begin
         Γ′ + (Δ′ + inc a)
      ≡⟨ sym (+-assoc Γ′ Δ′ (inc a)) ⟩
         Γ′ + Δ′ + inc a
      ≡⟨ cong (_+_ (Γ′ + Δ′)) (blah-preserves-inc 𝑎 Δ′ a) ⟩
         Γ′ + Δ′ + inc (blah 𝑎 Δ′ a)
      ∎

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ} {a₀ a₀′ : Action Γ} {𝑎 : a₀ ᴬ⌣ a₀′} {Γ′} {P P′ : Proc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) + Γ′)} {a R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , 𝑎 , Γ′ ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc _
         γ/E : ⋈[ Γ , 𝑎 , Γ′ + inc a ] (Proc↱ (+-assoc _ Γ′ (inc a)) R) R′
         E/γ : P′ —[ blah 𝑎 Γ′ a - ι ]→ Proc↱ (blah-preserves-inc-assoc 𝑎 Γ′ a) R′

   -- E can be the value of E/γ.
   bibble : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Γ′ a R →
            R ≅ Proc↱ (blah-preserves-inc-assoc 𝑎 Γ′ a) (Proc↱ (+-assoc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎))) Γ′ (inc a)) R)
   bibble {Γ} {a₀} 𝑎 Γ′ a R = ≅-sym (
      ≅-trans (Proc↲ (blah-preserves-inc-assoc 𝑎 Γ′ a) _)
              (Proc↲ (+-assoc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎))) Γ′ (inc a)) R))

   -- Heterogeneity quagmire. Starting to be a familiar pattern.
   ⊖′[_,_] : ∀ {ι Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Γ′ {P P′ : Proc (Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) + Γ′)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , 𝑎 , Γ′ ] P P′) → _Δ′_ {𝑎 = 𝑎} E γ
   ⊖′[ ˣ∇ˣ {x = x} {u = u} , Γ′ ] {P = P} {a = a} E refl =
      refl Δ subst (λ R → P —[ a - _ ]→ R) (≅-to-≡ (bibble (ˣ∇ˣ {x = x} {u = u}) Γ′ a _)) E
   ⊖′[ ᵇ∇ᵇ {a = a₀} {a₀′} , Γ′ ] {P = P} {a = a} {R} E refl =
      refl Δ subst (λ R → ((swap ᴿ+ Γ′) *) P —[ ((swap ᴿ+ Γ′) *) a - _ ]→ R) (≅-to-≡ (
         let open ≅-Reasoning in
         begin
            Proc↱ (ren-preserves-target (swap ᴿ+ Γ′) a) (((swap ᴿ+ Γ′ ᴿ+ inc a) *) R)
         ≅⟨ Proc↲ (ren-preserves-target (swap ᴿ+ Γ′) a) _ ⟩
            ((swap ᴿ+ Γ′ ᴿ+ inc a) *) R
         ≅⟨ ᴿ+-assoc swap Γ′ (inc a) R ⟩
            ((swap ᴿ+ (Γ′ + inc a)) *) (Proc↱ (+-assoc _ Γ′ (inc a)) R)
         ≅⟨ ≅-sym (Proc↲ (blah-preserves-inc-assoc (ᵇ∇ᵇ {a = a₀} {a₀′}) Γ′ a) _) ⟩
            Proc↱ (blah-preserves-inc-assoc (ᵇ∇ᵇ {a = a₀} {a₀′}) Γ′ a)
                  (((swap ᴿ+ (Γ′ + inc a)) *) (Proc↱ (+-assoc _ Γ′ (inc a)) R))
         ∎
         )) (((swap ᴿ+ Γ′) *′) E)
   ⊖′[ ᵇ∇ᶜ {a = a₀} {a₀′} , Γ′ ] {P = P} {a = a} E refl =
      refl Δ subst (λ R → P —[ a - _ ]→ R) (≅-to-≡ (bibble (ᵇ∇ᶜ {a = a₀} {a₀′}) Γ′ a _)) E
   ⊖′[ ᶜ∇ᵇ {a = a₀} {a₀′} , Γ′ ] {P = P} {a = a} E refl =
      refl Δ subst (λ R → P —[ a - _ ]→ R) (≅-to-≡ (bibble (ᶜ∇ᵇ {a = a₀} {a₀′}) Γ′ a _)) E
   ⊖′[ ᶜ∇ᶜ {a = a₀} {a₀′} , Γ′ ] {P = P} {a = a} E refl =
      refl Δ subst (λ R → P —[ a - _ ]→ R) (≅-to-≡ (bibble (ᶜ∇ᶜ {a = a₀} {a₀′}) Γ′ a _)) E
   ⊖′[ ᵛ∇ᵛ , Γ′ ] E φ = let φ/E Δ E/φ = ⊖ E (⋈-to-⋉ φ) in {!!} Δ {!!}
{-
   -- Hoped Agda would be able to infer ӓ and Γ′ from γ, but apparently not.
   ⊖′[_,_] : ∀ {ι Γ} (ӓ : Action₂ Γ) Γ′ {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) → _Δ′_ {ӓ = ӓ} {Γ′ = Γ′} E γ
   ⊖′[ ӓ , Γ′ ] {a = (_ •) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = (• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = • _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
-}
