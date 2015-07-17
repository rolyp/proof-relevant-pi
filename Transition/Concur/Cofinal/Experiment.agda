module Transition.Concur.Cofinal.Experiment where

   open import SharedModules

   open import Action using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖-✓)
   open import Name using (zero)
   open import Proc using (Proc↱)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Concur₁; ⊖₁; Delta)
   open import Transition.Concur.Cofinal using (⋈[_,_,_])

   blah : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) {a† S a‡ S′} (F : R —[ a† - _ ]→ S) (F′ : R —[ a‡ - _ ]→ S′) →
          ⋈[ Γ , 𝑎 , zero ] S (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) S′) → ⊖₁ 𝐸 ≡ F ᵀΔ F′
   blah = ?
