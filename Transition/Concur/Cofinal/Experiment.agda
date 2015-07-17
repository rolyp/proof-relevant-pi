module Transition.Concur.Cofinal.Experiment where

   open import SharedModules

   open import Action using (Action)
   open import Action.Concur using (_ᴬ⌣_; ᴬ⊖-✓)
   open import Name using (zero)
   open import Proc using (Proc↱)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (Concur₁; module Concur₁; ⊖₁; Delta); open Concur₁
   open import Transition.Concur.Cofinal using (⋈[_,_,_])

   blah : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) {S S′} (F : R —[ _ - _ ]→ S) (F′ : R′ —[ _ - _ ]→ S′) →
          ⋈[ Γ , 𝑎 , zero ] S (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) S′) → ⊖₁ 𝐸 ≡ F ᵀΔ F′
   blah (E ᵇ│ᵇ F) F₁ F′ q = {!!}
   blah (E ᵇ│ᶜ F) F₁ F′ q = {!!}
   blah (E ᶜ│ᵇ F) F₁ F′ q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ ᶜ│ Q) (F′ ᶜ│ .Q) refl = {!!}
   blah (E ᶜ│ᶜ F) (F₁ ᶜ│ Q) (P │ᶜ F′) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ ᶜ│ Q) (F′ │• F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ ᶜ│ Q) (F′ │ᵥ F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (R │ᶜ F₁) (F′ ᶜ│ S) q = {!!}
   blah (E ᶜ│ᶜ F) (R │ᶜ F₁) (P │ᶜ F′) q = {!!}
   blah (E ᶜ│ᶜ F) (R │ᶜ F₁) (F′ │• F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (R │ᶜ F₁) (F′ │ᵥ F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │• F₂) (F′ ᶜ│ S) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │• F₂) (P │ᶜ F′) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │• F₂) (F′ │• F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │• F₂) (F′ │ᵥ F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │ᵥ F₂) (F′ ᶜ│ S) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │ᵥ F₂) (P │ᶜ F′) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │ᵥ F₂) (F′ │• F′₁) q = {!!}
   blah (E ᶜ│ᶜ F) (F₁ │ᵥ F₂) (F′ │ᵥ F′₁) q = {!!}
   blah (𝐸 │•ᵇ F) F₁ F′ q = {!!}
   blah (𝐸 │•ᶜ F) F₁ F′ q = {!!}
   blah (E ᵇ│• 𝐸) F₁ F′₁ q = {!!}
   blah (E ᶜ│• 𝐸) F₁ F′₁ q = {!!}
   blah (𝐸 │ᵥᵇ F) F₁ F′ q = {!!}
   blah (𝐸 │ᵥᶜ F) F₁ F′ q = {!!}
   blah (E ᵇ│ᵥ 𝐸) F₁ F′₁ q = {!!}
   blah (E ᶜ│ᵥ 𝐸) F₁ F′₁ q = {!!}
   blah (𝐸 ➕₁ Q) F F′ q = {!!}
   blah (P │ᵇᵇ 𝐸) F₁ F′₁ q = {!!}
   blah (P │ᵇᶜ 𝐸) F₁ F′₁ q = {!!}
   blah (P │ᶜᵇ 𝐸) F₁ F′₁ q = {!!}
   blah (P │ᶜᶜ 𝐸) F₁ F′₁ q = {!!}
   blah (P │ᵛᵛ 𝐸) F₁ F′₁ q = {!!}
   blah (𝐸 ᵇᵇ│ Q) F F′ q = {!!}
   blah (𝐸 ᵇᶜ│ Q) F F′ q = {!!}
   blah (𝐸 ᶜᵇ│ Q) F F′ q = {!!}
   blah (𝐸 ᶜᶜ│ Q) F F′ q = {!!}
   blah (𝐸 ᵛᵛ│ Q) F F′ q = {!!}
   blah (𝐸 │• 𝐸₁) F₁ F′₁ q = {!!}
   blah (𝐸 │•ᵥ 𝐸₁) F₁ F′₁ q = {!!}
   blah (𝐸 │ᵥ• 𝐸₁) F₁ F′₁ q = {!!}
   blah (𝐸 │ᵥ 𝐸₁) F₁ F′₁ q = {!!}
   blah (𝐸 │ᵥ′ 𝐸₁) F₁ F′₁ q = {!!}
   blah (ν• 𝐸) F F′ q = {!!}
   blah (ν•ᵇ 𝐸) F F′ q = {!!}
   blah (ν•ᶜ 𝐸) F F′ q = {!!}
   blah (νᵇᵇ 𝐸) F F′ q = {!!}
   blah (νˣˣ 𝐸) F F′ q = {!!}
   blah (νᵇᶜ 𝐸) F F′ q = {!!}
   blah (νᶜᵇ 𝐸) F F′ q = {!!}
   blah (νᶜᶜ 𝐸) F F′ q = {!!}
   blah (νᵛᵛ 𝐸) F F′ q = {!!}
   blah (! 𝐸) F F′ q = {!!}
