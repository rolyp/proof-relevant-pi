module Transition.Concur.Transition.Properties where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.HeterogeneousEquality

   open import Action using (_ᴬ⌣_; ᴬ⌣-sym; Action; Action↱; Action↲; inc)
   open import Name using (zero; _+_; +-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
   import Proc.Ren
   open import Ren as ᴿ; open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Concur₁; module Delta′; Action₂; ᴬ⊖; ⊖₁);
      open Concur₁
   open import Transition.Concur.Cofinal using (⊖₁-✓; ⋈[_,_,_])
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; module _Δ′_)
   open import Transition.Concur.Ren using (/-preserves-ᴬ⌣)
   open import Transition.Concur.Transition using (/-preserves-⌣₁′)

   open Delta′
   open _Δ′_

   -- The 'cyclic' relationship between 𝐸, 𝐸′ and 𝐸″ means that E″ is mostly uninhabited for the asymmetric
   -- version of ⌣, and so any proof of this would be trivial. Need to rethink.
   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (𝐸 : E ⌣₁[ 𝑎 ] E′) (𝐸′ : E′ ⌣₁[ 𝑎′ ] E″) (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
          let 𝐸′/E = /-preserves-⌣₁′ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′
              gib : S (⊖₁ 𝐸″) —[ π₁ (ᴬ⊖ (/-preserves-ᴬ⌣ 𝑎″ 𝑎 (ᴬ⌣-sym 𝑎′))) - _ ]→ S (⊖₁ 𝐸/E″)
              gib = ≅-subst✴₃ Proc (λ P a R → P —[ a - _ ]→ R) refl ≅-refl ≅-refl ≅-refl (E′/E (⊖₁ 𝐸/E″))
              open _Δ′_
          in E/E′ (⊖₁ 𝐸′/E) ≅ E/γ (⊖′[ (a″ , π₁ (ᴬ⊖ 𝑎″)) , zero ] gib (⊖₁-✓ 𝐸″))
   blah _ _ _ = {!!}
