module Transition.Seq.Cofinal where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬΔ; ᴬ/); open _ᴬ⌣_
   open import Action.Ren using (ren-preserves-inc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆)
   open import Action.Seq.Ren using (ren-preserves-inc⋆)
   open import Braiding.Proc as ᴮ using (_⋉_; ⋈-to-⋉)
   open import Name as ᴺ using (_+_; +-assoc; zero)
   open import Ren as ᴿ using (Ren; _ᴿ+_; push; swap); open ᴿ.Renameable ⦃...⦄
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition using (_—[_-_]→_; source; target; action)
   open import Transition.Concur using (Concur; module Delta′; ⊖; ⌣-sym; module Properties)
   open import Transition.Concur.Cofinal using (﹙_,_,_,_﹚; ⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_; braid)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; source⋆; target⋆); open ᵀ⋆._—[_]→⋆_

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. Cofinality as a separate lemma.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Δ′ a⋆} {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) : Set where
      constructor _Δ_
      field
         {S S′} : _
         γ/E⋆ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ + inc⋆ a⋆ ﹚ (Proc↱ (+-assoc _ _ (inc⋆ a⋆)) R) S
         E⋆/γ : P′ —[ braid 𝑎 Δ′ a⋆ ]→⋆ S′

   -- Mostly case analysis which is glossed in the paper version.
   ⊖⋆[_,_] : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {a⋆ R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) → _Δ⋆_ 𝑎 E⋆ γ
   ⊖⋆[ ˣ∇ˣ , _ ] [] γ = γ Δ []
   ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ˣ∇ˣ {x = x} {u} , Δ′ ] E refl
   ... | γ/E Δ E/γ with ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ + 1 ] E⋆ γ/E
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ˣ∇ˣ {x = x} {u} , Δ′ ] E refl
   ... | γ/E Δ E/γ with ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ ] E⋆ γ/E
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᵇ∇ᵇ , _ ] [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} (ᵇ∇ᵇ {a = a} {a′}) Δ′ (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (subst (λ R′ → (source E/γ) —[ action E/γ - _ ]→ R′)
      (let open IsEquivalence isEquivalence using (reflexive) in ≅-to-≡ (
         Proc↲ (trans (reflexive (cong (_+_ (Γ + 1 + 1 + Δ′)) (ren-preserves-inc (swap ᴿ+ Δ′) (action E)))) refl) _)
      ) E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[_,_] {Γ} (ᵇ∇ᵇ {a = a} {a′}) Δ′ (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (subst (λ R′ → (source E/γ) —[ action E/γ - _ ]→ R′) (
      let open IsEquivalence isEquivalence using (reflexive) in ≅-to-≡ (
         Proc↲ (trans (reflexive (cong (_+_ (Γ + 1 + 1 + Δ′)) (ren-preserves-inc (swap ᴿ+ Δ′) (action E)))) refl) _)
      ) E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᵇ∇ᶜ , _ ] [] γ = γ Δ []
   ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᶜ∇ᵇ , _ ] [] γ = γ Δ []
   ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᶜ∇ᶜ , _ ] [] γ = γ Δ []
   ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E = refl Δ (E/γ ᶜ∷ E⋆/γ/E)
   -- Next two require a bit of heterogeneous equality shuffling.
   ⊖⋆[_,_] {Γ} ᵛ∇ᵛ Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ with ⊖′[ ᵛ∇ᵛ , Δ′ ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ᵛ∇ᵛ , Δ′ + 1 ] E⋆ γ/E
   ... | γ/E/E⋆ Δ E⋆/γ/E =
      let Γ′ = inc⋆ a⋆
          open ≅-Reasoning
          target⋆-E⋆ =
             begin
                Proc↱ (+-assoc Γ (Δ′ + 1) Γ′) (target⋆ E⋆)
             ≅⟨ Proc↲ (+-assoc Γ (Δ′ + 1) Γ′) _ ⟩
                target⋆ E⋆
             ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _) ⟩
                Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆)
             ≅⟨ ≅-sym (Proc↲ (+-assoc Γ Δ′ (1 + Γ′)) _) ⟩
                Proc↱ (+-assoc Γ Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆))
             ∎
          assoc₁ = cong (_+_ Γ) (+-assoc Δ′ 1 Γ′)
      in _Δ_ {S = Proc↱ assoc₁ (ᴮ.target γ/E/E⋆)}
      (≅-subst✴₂ Proc _⋉_ assoc₁ target⋆-E⋆ (≅-sym (Proc↲ assoc₁ _)) γ/E/E⋆)
      (E/γ ᵇ∷ E⋆/γ/E)
   ⊖⋆[_,_] {Γ} ᵛ∇ᵛ Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) γ with ⊖′[ ᵛ∇ᵛ , Δ′ ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ᵛ∇ᵛ , Δ′ ] E⋆ γ/E
   ... | γ/E/E⋆ Δ E⋆/γ/E =
      let Γ′ = inc⋆ a⋆
          open ≅-Reasoning
          target⋆-E⋆ =
             begin
                Proc↱ (+-assoc Γ (Δ′ + 0) Γ′) (target⋆ E⋆)
             ≅⟨ Proc↲ (+-assoc Γ (Δ′ + 0) Γ′) _ ⟩
                target⋆ E⋆
             ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _) ⟩
                Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆)
             ≅⟨ ≅-sym (Proc↲ (+-assoc Γ Δ′ (0 + Γ′)) _) ⟩
                Proc↱ (+-assoc Γ Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆))
             ∎
          assoc₀ = cong (_+_ Γ) (+-assoc Δ′ 0 (inc⋆ a⋆))
      in _Δ_ {S = Proc↱ assoc₀ (ᴮ.target γ/E/E⋆)}
      (≅-subst✴₂ Proc _⋉_ assoc₀ target⋆-E⋆ (≅-sym (Proc↲ assoc₀ _)) γ/E/E⋆)
      (E/γ ᶜ∷ E⋆/γ/E)
   ⊖⋆[ ᵛ∇ᵛ , _ ] [] γ = γ Δ []

   -- Trivial but painful exercise in heterogeneous equality.
   ⊖⋆-✓ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {a⋆ R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) → let open _Δ⋆_ in S (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ) ≅ S′ (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ)
   ⊖⋆-✓ ˣ∇ˣ _ [] _ = ≅-refl
   ⊖⋆-✓ ˣ∇ˣ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ˣ∇ˣ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᵇ _ [] _ = ≅-refl
   ⊖⋆-✓ ᵇ∇ᵇ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᵇ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᶜ _ [] _ = ≅-refl
   ⊖⋆-✓ ᵇ∇ᶜ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᶜ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᶜ∇ᵇ _ [] _ = ≅-refl
   ⊖⋆-✓ ᶜ∇ᵇ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᶜ∇ᵇ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᶜ∇ᶜ _ [] _ = ≅-refl
   ⊖⋆-✓ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᶜ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ = let open ≅-Reasoning in
      begin
         Proc↱ (+-assoc Γ Δ′ (1 + inc⋆ a⋆)) (Proc↱ (+-assoc (Γ + Δ′) 1 (inc⋆ a⋆)) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (1 + inc⋆ a⋆)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 (inc⋆ a⋆)) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 1 (inc⋆ a⋆)) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 1) (inc⋆ a⋆)) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 1) (inc⋆ a⋆)) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 1 (inc⋆ (id a⋆))) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 (inc⋆ (id a⋆))) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᶜ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ = let open ≅-Reasoning in
      begin
         Proc↱ (+-assoc Γ Δ′ (0 + inc⋆ a⋆)) (Proc↱ (+-assoc (Γ + Δ′) 0 (inc⋆ a⋆)) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (0 + inc⋆ a⋆)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 (inc⋆ a⋆)) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 0 (inc⋆ a⋆)) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 0) (inc⋆ a⋆)) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 0) (inc⋆ a⋆)) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 0 (inc⋆ (id a⋆))) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 (inc⋆ (id a⋆))) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ ᵛ∇ᵛ _ [] _ = ≅-refl
   ⊖⋆-✓ ᵛ∇ᵛ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵛ∇ᵛ Δ′ (E ᶜ∷ E⋆) γ = {!!}

{-
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
