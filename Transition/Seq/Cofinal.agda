module Transition.Seq.Cofinal where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬΔ; ᴬ/); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆)
   open import Action.Seq.Ren using (ren-preserves-inc⋆)
   open import Braiding.Proc using (_⋉_; ⋈-to-⋉)
   open import Name as ᴺ using (_+_; +-assoc; zero)
   open import Ren as ᴿ using (Ren; _ᴿ+_; push; swap); open ᴿ.Renameable ⦃...⦄
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition using (_—[_-_]→_; source; target)
   open import Transition.Concur using (Concur; module Delta′; ⊖; ⌣-sym; module Properties)
   open import Transition.Concur.Cofinal using (﹙_,_,_,_﹚; ⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_; braid; braid-preserves-inc-assoc)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; target⋆); open ᵀ⋆._—[_]→⋆_

   -- TODO: consolidate with similar lemmas for inc.
   braid-preserves-inc⋆ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in
                          inc⋆ ≃ₑ inc⋆ ∘ braid 𝑎 Δ′
   braid-preserves-inc⋆ ˣ∇ˣ _ _ = refl
   braid-preserves-inc⋆ ᵇ∇ᵇ Δ′ = ren-preserves-inc⋆ (swap ᴿ+ Δ′)
   braid-preserves-inc⋆ ᵇ∇ᶜ _ _ = refl
   braid-preserves-inc⋆ ᶜ∇ᵇ _ _ = refl
   braid-preserves-inc⋆ ᶜ∇ᶜ _ _ = refl
   braid-preserves-inc⋆ ᵛ∇ᵛ _ _ = refl

   braid-preserves-inc⋆-assoc : ∀ {Γ} {a₀ a₀′ : Action Γ} (𝑎 : a₀ ᴬ⌣ a₀′) Δ′ → let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)) in
                                (a⋆ : Action⋆ (Γ′ + Δ′)) → Γ′ + (Δ′ + inc⋆ a⋆) ≡ Γ′ + Δ′ + inc⋆ (braid 𝑎 Δ′ a⋆)
   braid-preserves-inc⋆-assoc {Γ} {a₀} 𝑎 Δ′ a⋆ =
      let Γ′ = Γ + inc a₀ + inc (π₁ (ᴬ⊖ 𝑎)); open EqReasoning (setoid _) in
      begin
         Γ′ + (Δ′ + inc⋆ a⋆)
      ≡⟨ sym (+-assoc Γ′ Δ′ (inc⋆ a⋆)) ⟩
         Γ′ + Δ′ + inc⋆ a⋆
      ≡⟨ cong (_+_ (Γ′ + Δ′)) (braid-preserves-inc⋆ 𝑎 Δ′ a⋆) ⟩
         Γ′ + Δ′ + inc⋆ (braid 𝑎 Δ′ a⋆)
      ∎

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. TODO: cofinality.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ′ a⋆} {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) : Set where
      constructor _Δ_
      field
         {S S′} : _
         γ/E⋆ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ + inc⋆ a⋆ ﹚ (Proc↱ (+-assoc _ _ (inc⋆ a⋆)) R) S
         E⋆/γ : P′ —[ braid 𝑎 Δ′ a⋆ ]→⋆ S′
{-
   -- Hetereogeneously equate braidings up to associativity of + on contexts.
   braid-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) Δ₁ Δ₂ Δ₃ S S′ →
                 (((ρ ᴿ+ (Δ₁ + Δ₂ + Δ₃))*)
                 (Proc↱ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) (Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S)) ≈ S′)
                 ≅
                 (((ρ ᴿ+ (Δ₁ + (Δ₂ + Δ₃)))*)
                 (Proc↱ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) (Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S)) ≈
                 Proc↱ (cong (_+_ Γ′) (+-assoc Δ₁ Δ₂ Δ₃)) S′)
   braid-assoc {Γ} {Γ′} ρ Δ₁ Δ₂ Δ₃ S S′ =
      ≅-cong₃ (λ Δ† P P′ → ((ρ ᴿ+ Δ†)*) P ≈ P′)
         (≡-to-≅ (+-assoc Δ₁ Δ₂ Δ₃))
         (
            let open ≅-Reasoning in
            begin
               Proc↱ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) (Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S)
            ≅⟨ Proc↲ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) _ ⟩
               Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S
            ≅⟨ Proc↲ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S ⟩
               S
            ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S) ⟩
               Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S
            ≅⟨ ≅-sym (Proc↲ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) _) ⟩
               Proc↱ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) (Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S)
            ∎
         )
         (≅-sym (Proc↲ (cong (_+_ Γ′) (+-assoc Δ₁ Δ₂ Δ₃)) S′))
-}

   -- Mostly case analysis which can be glossed in the paper version.
   ⊖⋆[_,_] : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {a⋆ R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) → _Δ⋆_ 𝑎 E⋆ γ
   ⊖⋆[ (ˣ∇ˣ {x = x} {u}) , Δ′ ] (E ᵇ∷ E⋆) refl = {!!}
   ⊖⋆[_,_] (ᵇ∇ᵇ {a = a} {a′}) Δ′ (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | γ/E Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ γ/E
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ {!!})
   ⊖⋆[ (ᵇ∇ᶜ {a = a} {a′}) , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ (ᶜ∇ᵇ {a = a} {a′}) , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ᵛ∇ᵛ , Δ′ ] (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆[ (ˣ∇ˣ {x = x} {u}) , Δ′ ] (E ᶜ∷ E⋆) refl = {!!}
   ⊖⋆[ ᵇ∇ᵇ , Δ′ ] (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆[ (ᵇ∇ᶜ {a = a} {a′}) , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ (ᶜ∇ᵇ {a = a} {a′}) , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ (ᶜ∇ᶜ {a = a} {a′}) , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᵛ∇ᵛ , Δ′ ] (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆[ ˣ∇ˣ , Δ′ ] [] γ = γ Δ []
   ⊖⋆[ ᵇ∇ᵇ , Δ′ ] [] γ = γ Δ []
   ⊖⋆[ ᵇ∇ᶜ , Δ′ ] [] γ = γ Δ []
   ⊖⋆[ ᶜ∇ᵇ , Δ′ ] [] γ = γ Δ []
   ⊖⋆[ ᶜ∇ᶜ , Δ′ ] [] γ = γ Δ []
   ⊖⋆[ ᵛ∇ᵛ , Δ′ ] [] γ = γ Δ []
{-
   ⊖⋆[ ӓ , m ] {a⋆ = a ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ with ⊖′[ ӓ , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ӓ , m + 1 ] E⋆ γ/E | ren-preserves-inc-assoc (braid ӓ) m (a ᵇ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl rewrite ≅-to-≡ (braid-assoc (braid ӓ) m 1 (inc⋆ a⋆) (target⋆ E⋆) S′) =
      let σ = braid ӓ
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᴬ⋆.ᵇ∷ ((σ ᴿ+ m ᴿ+ 1) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc↱ (+-assoc _ 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆)))
                         (Proc↱ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′)
                ≅⟨ Proc↲ (+-assoc _ 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆))) _ ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′
                ≅⟨ Proc↲ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′ ⟩
                   S′
                ≅⟨ ≅-sym (Proc↲ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′) ⟩
                   Proc↱ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′
                ≅⟨ ≅-sym (Proc↲ (ren-preserves-inc⋆-assoc σ m (a ᴬ⋆.ᵇ∷ a⋆)) _) ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m (a ᴬ⋆.ᵇ∷ a⋆))
                         (Proc↱ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᵇ∷ E⋆/γ/E)
      in γ/E/E⋆ Δ E/γ∷E⋆/γ/E
   ⊖⋆[ ӓ , m ] {a⋆ = a ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) γ with ⊖′[ ӓ , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ӓ , m ] E⋆ γ/E | ren-preserves-inc-assoc (braid ӓ) m (a ᶜ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl rewrite ≅-to-≡ (braid-assoc (braid ӓ) m 0 (inc⋆ a⋆) (target⋆ E⋆) S′) =
      let σ = braid ӓ
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᴬ⋆.ᶜ∷ ((σ ᴿ+ m) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc↱ (+-assoc _ 0 (inc⋆ (((σ ᴿ+ m) *) a⋆)))
                         (Proc↱ (ren-preserves-inc⋆-assoc σ m a⋆) S′)
                ≅⟨ Proc↲ (+-assoc _ 0 (inc⋆ (((σ ᴿ+ m) *) a⋆))) _ ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m a⋆) S′
                ≅⟨ Proc↲ (ren-preserves-inc⋆-assoc σ m a⋆) S′ ⟩
                   S′
                ≅⟨ ≅-sym (Proc↲ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′) ⟩
                   Proc↱ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′
                ≅⟨ ≅-sym (Proc↲ (ren-preserves-inc⋆-assoc σ m (a ᴬ⋆.ᶜ∷ a⋆)) _) ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m (a ᴬ⋆.ᶜ∷ a⋆))
                         (Proc↱ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᶜ∷ E⋆/γ/E)
      in γ/E/E⋆ Δ E/γ∷E⋆/γ/E

   -- Causal equivalence. TODO: eliminate redundancy in constructor signatures.
   infix 4 _≃_
   data _≃_ {Γ} {P : Proc Γ} : ∀ {a⋆ a′⋆ R R′} → P —[ a⋆ ]→⋆ R → P —[ a′⋆ ]→⋆ R′ → Set where
      -- Transposition cases, which can't be axioms without a way of extending a trace to the right.
      _ᶜ∶⇋∶ᶜ_[_]∷_ : ∀ {a a′} {R R′} (E : P —[ a ᶜ - _ ]→ R) (E′ : P —[ a′ ᶜ - _ ]→ R′) →
                     (E⌣E′ : E ⌣[ ᶜ∇ᶜ ] E′) → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                     ∀ {a⋆ S} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a⋆ ]→⋆ S} → E⋆ ≃ E′⋆ →
                     let _ Δ E′⋆/γ = ⊖⋆[ (a ᶜ , a′ ᶜ) , 0 ] E′⋆ (⊖-✓ E⌣E′) in
                     E ᶜ∷ E′/E ᶜ∷ E⋆ ≃ E′ ᶜ∷ E/E′ ᶜ∷ E′⋆/γ
      _ᶜ∶⇋∶ᵇ_[_]∷_ : ∀ {a a′} {R R′} (E : P —[ a ᶜ - _ ]→ R) (E′ : P —[ a′ ᵇ - _ ]→ R′) →
                    (E⌣E′ : E ⌣[ ᶜ∇ᵇ ] E′) → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                    ∀ {a⋆ S} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a⋆ ]→⋆ S} → E⋆ ≃ E′⋆ →
                    let _ Δ E′⋆/γ = ⊖⋆[ (a ᶜ , a′ ᵇ) , 0 ] E′⋆ (⊖-✓ E⌣E′) in
                    E ᶜ∷ E′/E ᵇ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᶜ∷ E′⋆/γ
      _ᵇ∶⇋∶ᵇ_[_]∷_ : ∀ {a a′} {R R′} (E : P —[ a ᵇ - _ ]→ R) (E′ : P —[ a′ ᵇ - _ ]→ R′) →
                    (E⌣E′ : E ⌣[ ᵇ∇ᵇ ] E′) → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                    ∀ {a⋆ S} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a⋆ ]→⋆ S} → E⋆ ≃ E′⋆ →
                    let _ Δ E′⋆/γ = ⊖⋆[ (a ᵇ , (push *) a′ ᵇ) , 0 ] E′⋆ (⊖-✓ E⌣E′) in
                    E ᵇ∷ E′/E ᵇ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᵇ∷ E′⋆/γ
      _ᵛ∶⇋∶ᵛ_[_]∷_ : ∀ {x u} {R R′} (E : P —[ (• x) ᵇ - _ ]→ R) (E′ : P —[ (• u) ᵇ - _ ]→ R′) →
                    (E⌣E′ : E ⌣[ ˣ∇ˣ ] E′) → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                    ∀ {a⋆ S} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a⋆ ]→⋆ S} → E⋆ ≃ E′⋆ →
                    let _ Δ E′⋆/γ = ⊖⋆[ ((• x) ᵇ , • ᴺ.suc u 〈 zero 〉 ᶜ) , 0 ] E′⋆ (⊖-✓ E⌣E′) in
                    E ᵇ∷ E′/E ᶜ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᶜ∷ E′⋆/γ
      -- Close under trace constructors.
      [] : [] ≃ []
      _ᵇ∷_ : ∀ {a a⋆ a′⋆ R S S′} (E : P —[ a ᵇ - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
             E⋆ ≃ E′⋆ → E ᵇ∷ E⋆ ≃ E ᵇ∷ E′⋆
      _ᶜ∷_ : ∀ {a a⋆ a′⋆ R S S′} (E : P —[ a ᶜ - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
             E⋆ ≃ E′⋆ → E ᶜ∷ E⋆ ≃ E ᶜ∷ E′⋆
      -- Transitivity and symmetry.
      ≃-trans : ∀ {a⋆ R a″⋆ S a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {F⋆ : P —[ a″⋆ ]→⋆ S} {E′⋆ : P —[ a′⋆ ]→⋆ R′} →
                E⋆ ≃ F⋆ → F⋆ ≃ E′⋆ → E⋆ ≃ E′⋆

   ≃-target : ∀ {Γ} {P : Proc Γ} {a⋆ a′⋆ R R′} {E : P —[ a⋆ ]→⋆ R} {E′ : P —[ a′⋆ ]→⋆ R′} → E ≃ E′ → P —[ a′⋆ ]→⋆ R′
   ≃-target {E′ = E′} _ = E′

   ≃-source : ∀ {Γ} {P : Proc Γ} {a⋆ a′⋆ R R′} {E : P —[ a⋆ ]→⋆ R} {E′ : P —[ a′⋆ ]→⋆ R′} → E ≃ E′ → P —[ a⋆ ]→⋆ R
   ≃-source {E = E} _ = E

   ≃-refl : ∀ {Γ} {P : Proc Γ} {a⋆ R} (E⋆ : P —[ a⋆ ]→⋆ R) → E⋆ ≃ E⋆
   ≃-refl [] = []
   ≃-refl (E ᵇ∷ E⋆) = E ᵇ∷ ≃-refl E⋆
   ≃-refl (E ᶜ∷ E⋆) = E ᶜ∷ ≃-refl E⋆

   open Delta′
   open Properties

   postulate
      -- Not trivial to prove, so come back to this.
      ≃-sym : ∀ {Γ} {P : Proc Γ} {a⋆ a′⋆ R R′} {E⋆ : P —[ a⋆ ]→⋆ R} {E′⋆ : P —[ a′⋆ ]→⋆ R′} → E⋆ ≃ E′⋆ → E′⋆ ≃ E⋆

   -- Existentially quantified version so we can state isEquivalence.
   TraceFrom : ∀ {Γ} (P : Proc Γ) → Set
   TraceFrom P = Σ[ a⋆ ∈ Action⋆ _ ] Σ[ R ∈ Proc _ ] P —[ a⋆ ]→⋆ R

   EquivFrom : ∀ {Γ} (P : Proc Γ) → TraceFrom P → TraceFrom P → Set
   EquivFrom _ (_ , _ , E⋆) (_ , _ , E′⋆) = E⋆ ≃ E′⋆

   ≃-isEquivalence : ∀ {Γ} {P : Proc Γ} → IsEquivalence (EquivFrom P)
   ≃-isEquivalence = record {
         refl = λ { {x = _ , _ , E⋆} → ≃-refl E⋆ };
         sym = ≃-sym;
         trans = ≃-trans
      }
-}
