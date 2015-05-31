module Transition.Concur.Properties2 where

   open import SharedModules

   open import Action as ᴬ using (Action; inc; _ᴬ⌣_); open ᴬ._ᴬ⌣_
   open import Name using (zero; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
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
   blah (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   blah (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = {!!}
   blah (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = {!!}
   blah (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᵇ (push *ᵇ) F
   blah (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᵇ F
   blah (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᶜ (push *ᶜ) F
   blah (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) with ⊖₁ E⌣E′
   ... | E′/E ᵀΔ _ = E′/E ᶜ│ᶜ F
   blah (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │•ᵇ F) (E⌣E″ │•ᵇ .F) with ⊖₁ E⌣E″ | blah E⌣E′ E′⌣E″ E⌣E″
   ... | E″/E ᵀΔ _ | E′/E⌣E″/E = {!!}
   blah (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │•ᶜ F) (E⌣E″ │•ᵇ .F) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   blah (E ᵇ│ᵇ F) (E′ ᵇ│• F′⌣F″) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   blah (E ᵇ│ᶜ F) (E′ ᶜ│• F′⌣F″) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   blah (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │ᵥᵇ F) (E⌣E″ │ᵥᵇ .F) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   blah (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᵇ .F) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᶜ (push *ᵇ) F
   blah (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ E′⌣E″) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   blah (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ E′⌣E″) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = E″/E ᶜ│ᵥ {!!}
   blah (E ᵇ│ᵇ F) (P │ᵇᵇ E′⌣E″) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ {!!}
   blah (E ᵇ│ᵇ F) (P │ᵇᶜ E′⌣E″) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ {!!}
   blah (E ᵇ│ᶜ F) (P │ᶜᶜ E′⌣E″) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ {!!}
   blah (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   blah (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   blah (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E ᶜᶜ│ (push *) Q
   blah (E⌣E′ │•ᵇ F) (E′⌣E″ │• F′⌣F″) (E⌣E″ │•ᵇ F′) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   blah (E⌣E′ │•ᵇ F) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │ᵥᵇ F′) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   blah (E⌣E′ │ᵥᵇ F) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │ᵥᵇ F′) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥ {!!}
   blah (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │•ᶜ F) (E⌣E″ │•ᶜ .F) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ = {!!}
   blah (E ᶜ│ᵇ F) (E′ ᵇ│• F′⌣F″) (E⌣E″ │•ᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   blah (E ᶜ│ᶜ F) (E′ ᶜ│• F′⌣F″) (E⌣E″ │•ᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = {!!}
   blah (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᶜ .F) with blah E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E │ᵥᶜ F
   blah (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = E″/E ᵇ│ᵥ F′⌣F″
   blah (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ F⌣F′) (E⌣E″ │ᵥᶜ F′) with ⊖₁ E⌣E″
   ... | E″/E ᵀΔ _ = E″/E ᶜ│ᵥ F⌣F′
   blah {a′⌣a″ = ᵛ∇ᵛ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   blah {a′⌣a″ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   blah (E ᶜ│ᵇ F) (P │ᵇᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ F′⌣F″
   blah (E ᶜ│ᶜ F) (P │ᶜᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = {!_!} │ᶜᶜ F′⌣F″
   blah (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᶜᶜ│ .Q) = {!!}
   blah (E⌣E′ │•ᶜ F) (E′⌣E″ │• F′⌣F″) (E⌣E″ │•ᶜ F′) = {!!}
   blah (E⌣E′ │•ᶜ F) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) = {!!}
   blah (E⌣E′ │ᵥᶜ F) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) = {!!}
   blah (P │ᵇᵇ F⌣F′) (E ᵇ│• F′⌣F″) (.E ᵇ│• F⌣F″) = {!!}
   blah (P │ᵇᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᵇ│• F⌣F″) = {!!}
   blah (P │ᵇᵇ F⌣F′) (E ᵇ│ᵥ F′⌣F″) (.E ᵇ│ᵥ F⌣F″) = {!!}
   blah (P │ᵇᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (.E ᵇ│ᵥ F⌣F″) = {!!}
   blah (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) = {!!}
   blah (P │ᵇᵇ F⌣F′) (.P │ᵇᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) = {!!}
   blah (P │ᵇᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) = {!!}
   blah (E ᵇ│• F⌣F′) (E′⌣E″ │• F′⌣F″) (E′ ᵇ│• F⌣F″) = {!!}
   blah (E ᵇ│• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E′ ᵇ│ᵥ F⌣F″) = {!!}
   blah (E ᵇ│ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E′ ᵇ│ᵥ F⌣F″) = {!!}
   blah (P │ᶜᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᶜ│• F⌣F″) with blah F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = _ ᶜ│• F′/F⌣F″/F
   blah {E = P │ᶜ F} E⌣E′ (E ᶜ│ᵥ F′⌣F″) E⌣E″ = {!!}
   blah (P │ᶜᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᶜᶜ F⌣F″) with blah F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = P │ᶜᶜ F′/F⌣F″/F
   blah (E ᶜ│• F⌣F′) (E′⌣E″ │• F′⌣F″) (E′ ᶜ│• F⌣F″) with blah F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = E′⌣E″ │• F′/F⌣F″/F
   blah {E = P │ᶜ F} (E ᶜ│• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) = {!!}
   blah {E = P │ᶜ F} (E ᶜ│ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) = {!!}
   blah (E⌣E′ │• F⌣F′) (E′⌣E″ │• F′⌣F″) (E⌣E″ │• F⌣F″) with blah E⌣E′ E′⌣E″ E⌣E″ | blah F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = {!!} │• F′/F⌣F″/F
   blah {E = E │• F} (E⌣E′ │• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″) = {!!}
   blah {E = E │• F} (E⌣E′ │•ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″) = {!!}
   blah {E = E │ᵥ F} (E⌣E′ │ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │ᵥ F⌣F″) = {!!}
   blah {E = ν• E} E⌣E′ (ν• E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (ν•ᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (ν•ᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵛᵛ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ν• E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵇᵇ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵛᵛ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᵇᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᵇ E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = νᶜ E} E⌣E′ (νᶜᶜ E′⌣E″) E⌣E″ = {!!}
   blah {E = ! E} E⌣E′ (! E′⌣E″) E⌣E″ = {!!}
