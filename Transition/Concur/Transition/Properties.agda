module Transition.Concur.Transition.Properties where

   open import SharedModules
   open import Ext
   open import Ext.Relation.Binary.HeterogeneousEquality
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.HeterogeneousEquality

   open import Action using (_ᴬ⌣_; ᴬ⌣-sym; Action; Action↱; Action↲; inc)
   open import Name using (zero; _+_; +-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
   import Proc.Ren
   open import Ren as ᴿ; open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; Action₂; ᴬ⊖; ⊖₁; inc₂; inc₂-def)
   open import Transition.Concur.Cofinal using (⊖₁-✓; ⋈[_,_,_])
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; module _Δ′_)
   open import Transition.Concur.Ren using (/-preserves-ᴬ⌣)
   open import Transition.Concur.Transition using (/-preserves-⌣₁′)

   open Delta′
   open _Δ′_

   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (𝐸 : E ⌣₁[ 𝑎 ] E′) (𝐸′ : E′ ⌣₁[ 𝑎′ ] E″) (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
          let 𝐸′/E = /-preserves-⌣₁′ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′
              a‡ = π₁ (ᴬ⊖ (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (ᴬ⌣-sym 𝑎′)))
              ӓ : Action₂ Γ
              ӓ = a″ , π₁ (ᴬ⊖ 𝑎″)
              a≈ : Γ + inc a″ + inc₂ (π₁ (ᴬ⊖ 𝑎″) , a‡) ≡ Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″)) + inc a‡
              a≈ = sym (+-assoc (Γ + inc a″) (inc (π₁ (ᴬ⊖ 𝑎″))) (inc a‡))
              P‡ : Proc (Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″)) + inc a‡)
              P‡ = Proc↱ a≈ (S (⊖₁ 𝐸/E″))
              E′/E″/E/E″ : Proc↱ (inc₂-def ӓ) (S (⊖₁ 𝐸″)) —[ a‡ - _ ]→ P‡
              E′/E″/E/E″ = E′/E (⊖₁ 𝐸/E″)
              a~ : Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) ≡ Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″))
              a~ = sym (+-assoc Γ (inc a″) (inc (π₁ (ᴬ⊖ 𝑎″))))
              blah′ : Γ + inc a″ + inc₂ (π₁ (ᴬ⊖ 𝑎″) , a‡) ≡ Γ + inc₂ ӓ + inc (subst Action (sym a~) a‡)
              blah′ =
                 let open EqReasoning (setoid _) in
                 begin
                    Γ + inc a″ + inc₂ (π₁ (ᴬ⊖ 𝑎″) , a‡)
                 ≡⟨ a≈ ⟩
                    Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″)) + inc a‡
                 ≡⟨ cong (λ Γ′ → Γ′ + inc a‡) (sym a~) ⟩
                    Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + inc a‡
                 ≡⟨ cong (λ Γ′ → Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + Γ′)
                    (≅-to-≡ (≅-cong✴ Action (sym (inc₂-def ӓ)) inc (≅-sym (Action↲ (sym (inc₂-def ӓ)) a‡)))) ⟩
                    Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + inc (Action↱ (sym (inc₂-def ӓ)) a‡)
                 ∎
              P† : Proc (Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + inc (Action↱ (sym (inc₂-def (a″ , π₁ (ᴬ⊖ 𝑎″)))) a‡))
              P† = Proc↱ blah′ (S (⊖₁ 𝐸/E″))
              gib : S (⊖₁ 𝐸″) —[ Action↱ (sym (inc₂-def ӓ)) a‡ - _ ]→ P†
              gib = {!!}
              open ≅-Reasoning
              quib : (S (⊖₁ 𝐸″) —[ Action↱ (sym (inc₂-def ӓ)) a‡ - _ ]→ P†) ≅
                     (Proc↱ (inc₂-def ӓ) (S (⊖₁ 𝐸″)) —[ a‡ - _ ]→ P‡)
              quib =
                 begin
                    (S (⊖₁ 𝐸″) —[ Action↱ (sym (inc₂-def ӓ)) a‡ - _ ]→ P†)
                 ≅⟨ ≅-cong✴₃ Proc a~ (λ P a R → P —[ a - _ ]→ R)
                             (≅-sym (Proc↲ a~ (S (⊖₁ 𝐸″)))) (Action↲ (sym a~) a‡)
                             (begin
                                 Proc↱ blah′ (S (⊖₁ (/-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′)))
                              ≅⟨ Proc↲ blah′ _ ⟩
                                 S (⊖₁ (/-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′))
                              ≅⟨ ≅-sym (Proc↲ a≈ _) ⟩
                                 Proc↱ a≈ (S (⊖₁ (/-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′)))
                              ∎) ⟩
                    (Proc↱ (inc₂-def ӓ) (S (⊖₁ 𝐸″)) —[ a‡ - _ ]→ P‡)
                 ∎
              open _Δ′_
          in E/E′ (⊖₁ 𝐸′/E) ≅ E/γ (⊖′[ (a″ , π₁ (ᴬ⊖ 𝑎″)) , zero ] gib (⊖₁-✓ 𝐸″))
   blah _ _ _ = {!!}
