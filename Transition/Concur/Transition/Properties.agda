module Transition.Concur.Transition.Properties where

   open import SharedModules
   open import Ext
   import Relation.Binary.HeterogeneousEquality
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action using (_ᴬ⌣_; ᴬ⌣-sym; Action; inc)
   open import Name using (zero; _+_; +-assoc)
   open import Proc using (Proc; Proc↲)
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
              γ : ⋈[ Γ , (a″ , π₁ (ᴬ⊖ 𝑎″)) , zero ] (S (⊖₁ 𝐸″)) (S′ (⊖₁ 𝐸″))
              γ = ⊖₁-✓ 𝐸″
              a‡ = π₁ (ᴬ⊖ (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (ᴬ⌣-sym 𝑎′)))
              ӓ : Action₂ Γ
              ӓ = a″ , π₁ (ᴬ⊖ 𝑎″)
              zib : Γ + inc a″ + inc₂ (π₁ (ᴬ⊖ 𝑎″) , a‡) ≡ Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″)) + inc a‡
              zib = sym (+-assoc (Γ + inc a″) (inc (π₁ (ᴬ⊖ 𝑎″))) (inc a‡))
              E′/E″/E/E″ : Proc↱ (inc₂-def ӓ) (S (⊖₁ 𝐸″)) —[ a‡ - _ ]→ Proc↱ zib (S (⊖₁ 𝐸/E″))
              E′/E″/E/E″ = E′/E (⊖₁ 𝐸/E″)
              a† : Action (Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)))
              a† = Action↱ (sym (inc₂-def ӓ)) a‡
              open EqReasoning (setoid _)
              bib : inc a‡ ≡ inc (Action↱ (sym (inc₂-def ӓ)) a‡)
              bib = ≅-to-≡ (hcong (sym (inc₂-def ӓ)) inc (≅-sym (Action↲ (sym (inc₂-def ӓ)) a‡)))
              gib : S (⊖₁ 𝐸″) —[ a† - _ ]→ flip Proc↱ (S (⊖₁ 𝐸/E″)) (
                 begin
                    Γ + inc a″ + inc₂ (π₁ (ᴬ⊖ 𝑎″) , a‡)
                 ≡⟨ sym (+-assoc _ _ (inc a‡)) ⟩
                    Γ + inc a″ + inc (π₁ (ᴬ⊖ 𝑎″)) + inc a‡
                 ≡⟨ cong (λ Γ′ → Γ′ + inc a‡) (+-assoc _ _ (inc (π₁ (ᴬ⊖ 𝑎″)))) ⟩
                    Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + inc a‡
                 ≡⟨ cong (λ Γ′ → Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + Γ′) bib ⟩
                    Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)) + inc (Action↱ (sym (inc₂-def ӓ)) a‡)
                 ∎)
              gib = {!!}
              open _Δ′_
          in E/E′ (⊖₁ 𝐸′/E) ≅ E/γ (⊖′[ (a″ , π₁ (ᴬ⊖ 𝑎″)) , zero ] gib γ)
   blah _ _ _ = {!!}
