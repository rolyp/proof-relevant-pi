module Transition.Seq.Cofinal.Cofinal where

   open import ProofRelevantPiCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬΔ; ᴬ/); open _ᴬ⌣_
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆)
   open import Braiding.Proc as ᴮ using (_⋉_; ⋉̂-to-⋉; target)
   open import Braiding.Transition using (_Δ⁼_; _Δ_; ⊖)
   open import Name as ᴺ using (Cxt; _+_; +-assoc; zero)
   open import Proc using (Proc; Proc↱; Proc↲)
   open import Ren as ᴿ using (suc; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Transition.Concur.Cofinal using (⋈[_,_,_,_]; γ)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_; braid)
   open import Transition.Seq as ᵀ⋆ using (_—[_]→⋆_; source⋆; target⋆); open ᵀ⋆._—[_]→⋆_
   open import Transition.Seq.Cofinal using (_Δ⋆_; module _Δ⋆_; _Δ_; ⊖⋆[_,_])

   ≅-cong-swap : ∀ {Γ Δ′ Δ″ : Cxt} {P : Proc (Γ + 2 + Δ′)} {P′ : Proc (Γ + 2 + Δ″)} →
                 Δ′ ≡ Δ″ → P ≅ P′ → ((swap ᴿ+ Δ′) *) P ≅ ((swap ᴿ+ Δ″) *) P′
   ≅-cong-swap = λ { {Δ′ = _} refl ≅-refl → ≅-refl }

   -- Painful exercise in heterogeneous equality. TODO: consolidate ˣ∇ˣ, ᵇ∇ᶜ and ᶜ∇ᵇ cases, which are identical.
   γ⋆ : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Δ′)} {a⋆ R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ _⋉_ , Γ , 𝑎 , Δ′ ] P P′) →
          let open _Δ⋆_ in S (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ) ≅ S′ (⊖⋆[ 𝑎 , Δ′ ] E⋆ γ)
   γ⋆ ˣ∇ˣ _ [] _ = ≅-refl
   γ⋆ {Γ} (ˣ∇ˣ {x = x} {u}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ˣ∇ˣ {x = x} {u} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ + 1 ] E⋆ refl | γ⋆ (ˣ∇ˣ {x = x} {u}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ {Γ} (ˣ∇ˣ {x = x} {u}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ˣ∇ˣ {x = x} {u} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ˣ∇ˣ {x = x} {u} , Δ′ ] E⋆ refl | γ⋆ (ˣ∇ˣ {x = x} {u}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ ᵇ∇ᵇ _ [] _ = ≅-refl
   γ⋆ {Γ} (ᵇ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | γ⋆ (ᵇ∇ᵇ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         ((swap ᴿ+ (Δ′ + (1 + Γ′))) *)
         (Proc↱ (+-assoc (Γ + 2) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 2 + Δ′) 1 Γ′) (target⋆ E⋆)))
      ≅⟨ ≅-cong-swap (sym (+-assoc Δ′ 1 Γ′))
         (begin
            Proc↱ (+-assoc (Γ + 2) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 2 + Δ′) 1 Γ′) (target⋆ E⋆))
         ≅⟨ Proc↲ (+-assoc (Γ + 2) Δ′ (1 + Γ′)) _ ⟩
            Proc↱ (+-assoc (Γ + 2 + Δ′) 1 Γ′) (target⋆ E⋆)
         ≅⟨ Proc↲ (+-assoc (Γ + 2 + Δ′) 1 Γ′) _ ⟩
            target⋆ E⋆
         ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 2) (Δ′ + 1) Γ′) _) ⟩
            Proc↱ (+-assoc (Γ + 2) (Δ′ + 1) Γ′) (target⋆ E⋆)
         ∎) ⟩
         ((swap ᴿ+ (Δ′ + 1 + Γ′)) *) (Proc↱ (+-assoc (Γ + 2) (Δ′ + 1) Γ′) (target⋆ E⋆))
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 2 + Δ′) 1 (inc⋆ ((suc (swap ᴿ+ Δ′) *) a⋆))) _) ⟩
         Proc↱ (+-assoc (Γ + 2 + Δ′) 1 (inc⋆ ((suc (swap ᴿ+ Δ′) *) a⋆))) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ {Γ} (ᵇ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl | γ⋆ (ᵇ∇ᵇ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         ((swap ᴿ+ (Δ′ + (0 + Γ′))) *)
         (Proc↱ (+-assoc (Γ + 2) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 2 + Δ′) 0 Γ′) (target⋆ E⋆)))
      ≅⟨ ≅-cong-swap (sym (+-assoc Δ′ 0 Γ′))
         (begin
            Proc↱ (+-assoc (Γ + 2) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 2 + Δ′) 0 Γ′) (target⋆ E⋆))
         ≅⟨ Proc↲ (+-assoc (Γ + 2) Δ′ (0 + Γ′)) _ ⟩
            Proc↱ (+-assoc (Γ + 2 + Δ′) 0 Γ′) (target⋆ E⋆)
         ≅⟨ Proc↲ (+-assoc (Γ + 2 + Δ′) 0 Γ′) _ ⟩
            target⋆ E⋆
         ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 2) (Δ′ + 0) Γ′) _) ⟩
            Proc↱ (+-assoc (Γ + 2) (Δ′ + 0) Γ′) (target⋆ E⋆)
         ∎) ⟩
         ((swap ᴿ+ (Δ′ + 0 + Γ′)) *) (Proc↱ (+-assoc (Γ + 2) (Δ′ + 0) Γ′) (target⋆ E⋆))
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 2 + Δ′) 0 (inc⋆ (((swap ᴿ+ Δ′) *) a⋆))) _) ⟩
         Proc↱ (+-assoc (Γ + 2 + Δ′) 0 (inc⋆ (((swap ᴿ+ Δ′) *) a⋆))) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ ᵇ∇ᶜ _ [] _ = ≅-refl
   γ⋆ {Γ} (ᵇ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | γ⋆ (ᵇ∇ᶜ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ {Γ} (ᵇ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᵇ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl | γ⋆ (ᵇ∇ᶜ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ ᶜ∇ᵇ _ [] _ = ≅-refl
   γ⋆ {Γ} (ᶜ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | γ⋆ (ᶜ∇ᵇ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ {Γ} (ᶜ∇ᵇ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᵇ {a = a} {a′} , Δ′ ] E⋆ refl | γ⋆ (ᶜ∇ᵇ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc (Γ + 1) Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1) (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + 1 + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + 1 + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ ᶜ∇ᶜ _ [] _ = ≅-refl
   γ⋆ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ + 1 ] E⋆ refl | γ⋆ (ᶜ∇ᶜ {a = a} {a′}) (Δ′ + 1) E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc Γ Δ′ (1 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (1 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 1) Γ′) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 1) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ {Γ} (ᶜ∇ᶜ {a = a} {a′}) Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) refl with ⊖′[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E refl
   ... | refl Δ E/γ with ⊖⋆[ ᶜ∇ᶜ {a = a} {a′} , Δ′ ] E⋆ refl | γ⋆ (ᶜ∇ᶜ {a = a} {a′}) Δ′ E⋆ refl
   ... | _Δ_ {._} refl E⋆/γ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (+-assoc Γ Δ′ (0 + Γ′)) (Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆))
      ≅⟨ Proc↲ (+-assoc Γ Δ′ (0 + Γ′)) _ ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆)
      ≅⟨ Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _ ⟩
         target⋆ E⋆
      ≅⟨ ≅-sym (Proc↲ (+-assoc Γ (Δ′ + 0) Γ′) _) ⟩
         Proc↱ (+-assoc Γ (Δ′ + 0) Γ′) (target⋆ E⋆)
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/γ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆/γ/E)
      ∎
   γ⋆ ᵛ∇ᵛ _ [] _ = ≅-refl
   γ⋆ {Γ} ᵛ∇ᵛ Δ′ {a⋆ = _ ᴬ⋆.ᵇ∷ a⋆} (E ᵇ∷ E⋆) φ with ⊖ E φ
   ... | φ/E Δ E/φ with ⊖⋆[ ᵛ∇ᵛ , Δ′ + 1 ] E⋆ φ/E | γ⋆ ᵛ∇ᵛ (Δ′ + 1) E⋆ φ/E
   ... | φ/E/E⋆ Δ E⋆/φ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (cong (_+_ Γ) (+-assoc Δ′ 1 Γ′)) (target φ/E/E⋆)
      ≅⟨ Proc↲ (cong (_+_ Γ) (+-assoc Δ′ 1 Γ′)) _ ⟩
         target φ/E/E⋆
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/φ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 1 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 1 Γ′) (target⋆ E⋆/φ/E)
      ∎
   γ⋆ {Γ} ᵛ∇ᵛ Δ′ {a⋆ = _ ᴬ⋆.ᶜ∷ a⋆} (E ᶜ∷ E⋆) φ with ⊖ E φ
   ... | φ/E Δ E/φ with ⊖⋆[ ᵛ∇ᵛ , Δ′ ] E⋆ φ/E | γ⋆ ᵛ∇ᵛ Δ′ E⋆ φ/E
   ... | φ/E/E⋆ Δ E⋆/φ/E | γ⋆′ =
      let open ≅-Reasoning; Γ′ = inc⋆ a⋆ in
      begin
         Proc↱ (cong (_+_ Γ) (+-assoc Δ′ 0 Γ′)) (target φ/E/E⋆)
      ≅⟨ Proc↲ (cong (_+_ Γ) (+-assoc Δ′ 0 Γ′)) _ ⟩
         target φ/E/E⋆
      ≅⟨ γ⋆′ ⟩
         target⋆ E⋆/φ/E
      ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ′) 0 Γ′) _) ⟩
         Proc↱ (+-assoc (Γ + Δ′) 0 Γ′) (target⋆ E⋆/φ/E)
      ∎
