module Transition.Seq.Cofinal.Cofinal where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬΔ; ᴬ/); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆)
   open import Braiding.Proc as ᴮ using (_⋉_; ⋈-to-⋉)
   open import Name as ᴺ using (_+_; +-assoc; zero)
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Transition.Concur.Cofinal using (﹙_,_,_,_﹚; ⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_; braid)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; source⋆; target⋆); open ᵀ⋆._—[_]→⋆_
   open import Transition.Seq.Cofinal using (_Δ⋆_; module _Δ⋆_; _Δ_; ⊖⋆[_,_])

   -- Trivial but painful exercise in heterogeneous equality.
   ⊖⋆-✓ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {a⋆ R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ﹙ _⋉_ , Γ , 𝑎 , Δ′ ﹚ P P′) → let open _Δ⋆_ in S (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ) ≅ S′ (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ)
   ⊖⋆-✓ ˣ∇ˣ _ [] _ = ≅-refl
   ⊖⋆-✓ ˣ∇ˣ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ˣ∇ˣ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᵇ _ [] _ = ≅-refl
   ⊖⋆-✓ {Γ} (ᵇ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | ⊖⋆-✓ (ᵇ∇ᵇ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         {!!}
      ≅⟨ {!!} ⟩
         {!!}
      ∎
   ⊖⋆-✓ ᵇ∇ᵇ Δ′ (E ᶜ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵇ∇ᶜ _ [] _ = ≅-refl
   ⊖⋆-✓ {Γ} (ᵇ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | ⊖⋆-✓ (ᵇ∇ᶜ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ {Γ} (ᵇ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl | ⊖⋆-✓ (ᵇ∇ᶜ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ ᶜ∇ᵇ _ [] _ = ≅-refl
   ⊖⋆-✓ {Γ} (ᶜ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᵇ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ {Γ} (ᶜ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᵇ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ ᶜ∇ᶜ _ [] _ = ≅-refl
   ⊖⋆-✓ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᶜ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc Γ Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl | ⊖⋆-✓ (ᶜ∇ᶜ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | ⊖⋆-✓′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc Γ Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ ⊖⋆-✓′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   ⊖⋆-✓ ᵛ∇ᵛ _ [] _ = ≅-refl
   ⊖⋆-✓ ᵛ∇ᵛ Δ′ (E ᵇ∷ E⋆) γ = {!!}
   ⊖⋆-✓ ᵛ∇ᵛ Δ′ (E ᶜ∷ E⋆) γ = {!!}
