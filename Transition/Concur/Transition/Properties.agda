module Transition.Concur.Transition.Properties where

   open import SharedModules

   open import Action using (_ᴬ⌣_)
   open import Proc using (Proc)
   import Proc.Ren
   open import Ren as ᴿ; open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≈_)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; module Delta′; ⊖₁)
   open import Transition.Concur.Cofinal using (⊖₁-✓; ⋈[_,_,_])
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; module _Δ′_)
   open import Transition.Concur.Transition using (/-preserves-⌣₁′)

   open Delta′
   open _Δ′_

   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (𝐸 : E ⌣₁[ 𝑎 ] E′) (𝐸′ : E′ ⌣₁[ 𝑎′ ] E″) (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
          let 𝐸′/E = /-preserves-⌣₁′ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣₁′ 𝐸″ 𝐸 𝐸′
              γ : (Transition.Concur.Cofinal.braid (a″ , π₁ (Transition.Concur.ᴬ⊖ 𝑎″)) *) (S (⊖₁ 𝐸″)) ≈ S′ (⊖₁ 𝐸″)
              γ = ⊖₁-✓ 𝐸″
              bib = ⊖′[ {!!} , {!!} ] (E′/E (⊖₁ 𝐸′/E)) {!γ!} in
          E/E′ (⊖₁ 𝐸′/E) ≅ E′/E (⊖₁ 𝐸/E″)
   blah _ _ _ = {!!}
