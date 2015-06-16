module Transition.Concur.Transition.Properties where

   open import SharedModules
   import Relation.Binary.HeterogeneousEquality

   open import Action using (_ᴬ⌣_; Action)
   open import Name using (zero; _+_)
   open import Proc using (Proc; Proc↲)
   import Proc.Ren
   open import Ren as ᴿ; open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ᴬ⊖; ⊖₁; inc₂; inc₂-def)
   open import Transition.Concur.Cofinal using (⊖₁-✓; ⋈[_,_,_])
   open import Transition.Concur.Cofinal.Transition using (⊖′; module _Δ′_)
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
              E′/E″/E/E″ : subst Proc (inc₂-def 𝑎″) (S (⊖₁ 𝐸″)) —[ π₁ (ᴬ⊖ (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (Action.ᴬ⌣-sym 𝑎′))) - _ ]→
                          subst Proc (inc₂-def (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (Action.ᴬ⌣-sym 𝑎′))) (S (⊖₁ 𝐸/E″))
              E′/E″/E/E″ = E′/E (⊖₁ 𝐸/E″)
              a† : Action (Γ + inc₂ (a″ , π₁ (ᴬ⊖ 𝑎″)))
              a† = subst Action (sym (inc₂-def 𝑎″)) (π₁ (ᴬ⊖ (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (Action.ᴬ⌣-sym 𝑎′))))
              gib : S (⊖₁ 𝐸″) —[ a† - _ ]→ subst Proc {!!} (S (⊖₁ 𝐸/E″))
              gib = {!!}
              open ≅-Reasoning
              bib = ⊖′ gib γ
          in E/E′ (⊖₁ 𝐸′/E) ≅ E′/E″/E/E″
   blah _ _ _ = {!!}
