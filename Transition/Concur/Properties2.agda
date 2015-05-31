module Transition.Concur.Properties2 where

   open import SharedModules

   open import Action as ᴬ using (Action; inc; _ᴬ⌣_); open ᴬ._ᴬ⌣_
   open import Name using (zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Concur using (ᴬ⊖; Concur₁; module Concur₁; Delta′; Delta; ⊖₁; ⌣-sym); open Concur₁

   -- Only in the two ᵛ∇ᵛ cases is the outcome not uniquely determined by the types; in each case
   -- extrusions of the same binder are preserved.
   bib : ∀ {Γ} {a a′ a″ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) (a′⌣a″ : a′ ᴬ⌣ a″) (a⌣a″ : a ᴬ⌣ a″) →
         π₁ (ᴬ⊖ a⌣a′) ᴬ⌣ π₁ (ᴬ⊖ a⌣a″)
   bib ᵛ∇ᵛ ᵛ∇ᵛ ᵛ∇ᵛ = ᶜ∇ᶜ
   bib ᵛ∇ᵛ ᵛ∇ᵛ ᵇ∇ᵇ = ᶜ∇ᵇ
   bib ᵛ∇ᵛ ᵇ∇ᵇ ᵛ∇ᵛ = ᶜ∇ᶜ
   bib ᵛ∇ᵛ ᵇ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   bib ᵛ∇ᵛ ᵇ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   bib ᵇ∇ᵇ ᵛ∇ᵛ ᵛ∇ᵛ = ᵇ∇ᶜ
   bib ᵇ∇ᵇ ᵛ∇ᵛ ᵇ∇ᵇ = ᵛ∇ᵛ
   bib ᵇ∇ᵇ ᵇ∇ᵇ ᵛ∇ᵛ = ᵇ∇ᶜ
   bib ᵇ∇ᵇ ᵇ∇ᵇ ᵇ∇ᵇ = ᵇ∇ᵇ
   bib ᵇ∇ᵇ ᵇ∇ᶜ ᵇ∇ᶜ = ᵇ∇ᶜ
   bib ᵇ∇ᶜ ᶜ∇ᵇ ᵛ∇ᵛ = ᶜ∇ᶜ
   bib ᵇ∇ᶜ ᶜ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   bib ᵇ∇ᶜ ᶜ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   bib ᶜ∇ᵇ ᵛ∇ᵛ ᶜ∇ᵇ = ᵛ∇ᵛ
   bib ᶜ∇ᵇ ᵇ∇ᵇ ᶜ∇ᵇ = ᵇ∇ᵇ
   bib ᶜ∇ᵇ ᵇ∇ᶜ ᶜ∇ᶜ = ᵇ∇ᶜ
   bib ᶜ∇ᶜ ᶜ∇ᵇ ᶜ∇ᵇ = ᶜ∇ᵇ
   bib ᶜ∇ᶜ ᶜ∇ᶜ ᶜ∇ᶜ = ᶜ∇ᶜ

   -- Residuation preserves concurrency.
   blah : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
          {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → E′ ⌣₁[ a′⌣a″ ] E″ → (E⌣E″ : E ⌣₁[ a⌣a″ ] E″) →
          Delta′.E′/E (⊖₁ E⌣E′) ⌣₁[ bib a⌣a′ a′⌣a″ a⌣a″ ] Delta′.E′/E (⊖₁ E⌣E″)
   blah {E = x •∙ ._} E⌣E′ () E⌣E″
   blah {E = • x 〈 y 〉∙ ._} E⌣E′ () E⌣E″
   blah {E = E ➕₁ .Q} E⌣E′ (E′⌣E″ ➕₁ Q) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E₁ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᵇ│ .Q} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = E ᵇ│ .Q} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = E ᵇ│ .Q} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E ᵇ│ Q} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E₁ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E ᶜ│ .Q} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = E ᶜ│ .Q} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = E ᶜ│ .Q} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E ᶜ│ Q} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E₁ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᵇ E} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᵇ E} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᵇ E} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᵇ E} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E₁ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E₁ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E₁ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = P │ᶜ E} () (E₁ ᶜ│ᶜ F) E⌣E″
   blah {E = P │ᶜ E} () (E′⌣E″ │•ᵇ F) E⌣E″
   blah {E = P │ᶜ E} () (E′⌣E″ │•ᶜ F) E⌣E″
   blah {E = P │ᶜ E} () (E₁ ᵇ│• E′⌣E″) E⌣E″
   blah {E = .P │ᶜ F} (P │ᶜᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᶜ│• F⌣F″) with ⊖₁ F⌣F′ | ⊖₁ F⌣F″
   ... | F′/F ᵀΔ _ | F″/F ᵀΔ _ = let x = blah F⌣F′ F′⌣F″ F⌣F″ in _ ᶜ│• {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E₁ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E₁ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᶜ E} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᶜ E} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = .P │ᶜ E} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = P │ᶜ E} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E₂ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E₂ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E₂ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = E₁ │• E} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │• E₁} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E₂ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E₂ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E₂ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = E₁ •│ E} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E •│ E₁} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᵇ│ᵇ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᵇ│ᶜ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᶜ│ᵇ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᶜ│ᶜ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E′⌣E″ │•ᵇ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E′⌣E″ │•ᶜ F) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᵇ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E₂ ᶜ│• E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E′⌣E″ │ᵥᵇ F) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E′⌣E″ │ᵥᶜ F) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E₂ ᵇ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E₂ ᶜ│ᵥ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (P │ᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (P │ᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (P │ᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E′⌣E″ ᵇᵇ│ Q) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E′⌣E″ ᵇᶜ│ Q) E⌣E″ = {!!}
   blah {E = E₁ │ᵥ E} E⌣E′ (E′⌣E″ ᶜᶜ│ Q) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E′⌣E″ │• E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E′⌣E″ │•ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = E │ᵥ E₁} E⌣E′ (E′⌣E″ │ᵥ E′⌣E″₁) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (ν• E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (ν•ᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (ν•ᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵛᵛ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (ν• E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (ν•ᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (ν•ᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵛᵛ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (ν• E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (ν•ᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (ν•ᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (νᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (νᵛᵛ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (νᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ! E} E⌣E′ (! E′⌣E″) E⌣E″ = {!!}
