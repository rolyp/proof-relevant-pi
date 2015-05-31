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
   blah {P = Ο} () _ _
   blah {P = _ •∙ _} () _ _
   blah {P = • _ 〈 _ 〉∙ _} () _ _
   blah {P = P ➕ Q} {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {P = P │ Q} {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {P = ν P} {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {P = ! P} {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!} --
{-
   blah {P = P ➕ .Q} {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) |
        (• ._ 〈 .zero 〉∙ S) ᵀΔ _ | (• ._ 〈 .zero 〉∙ .S) ᵀΔ _ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | E′/E ➕₁ Q₁ ᵀΔ _ | E′/E₁ ➕₁ .Q₁ ᵀΔ _ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | E′/E ᶜ│ Q₁ ᵀΔ E/E′ | E′/E₁ ᶜ│ .Q₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | P₁ │ᶜ E′/E ᵀΔ  E/E′ | E′/E₁ ᶜ│ Q₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | E′/E ᶜ│ Q₁ ᵀΔ E/E′ | P₁ │ᶜ E′/E₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | P₁ │ᶜ E′/E ᵀΔ E/E′ | .P₁ │ᶜ E′/E₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | νᶜ E′/E ᵀΔ E/E′ | νᶜ E′/E₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) | E′/E ᵀΔ E/E′ | ! E′/E₁ ᵀΔ E/E′₁ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (P │ᵇᵇ E⌣E′) (.P │ᵇᵇ E′⌣E″) (.P │ᵇᵇ E⌣E″) | q | r = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) | q | r = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (ν• E⌣E′) (ν• E′⌣E″) (ν• E⌣E″) | q | r = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (νᵛᵛ E⌣E′) (νᵛᵛ E′⌣E″) (νᵛᵛ E⌣E″) | q | r = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (! E⌣E′) (! E′⌣E″) (! E⌣E″) | q | r = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵇ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᶜ} {ᵇ∇ᶜ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᵇ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᵇ} {ᵛ∇ᵛ} {ᵇ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᵇ} {ᵇ∇ᵇ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᵇ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᵇ} {ᵇ∇ᶜ} {ᵇ∇ᶜ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᶜ} {ᶜ∇ᵇ} {ᵛ∇ᵛ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᶜ} {ᶜ∇ᵇ} {ᵇ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᵇ∇ᶜ} {ᶜ∇ᶜ} {ᵇ∇ᶜ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᶜ∇ᵇ} {ᵛ∇ᵛ} {ᶜ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᶜ∇ᵇ} {ᵇ∇ᵇ} {ᶜ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᶜ∇ᵇ} {ᵇ∇ᶜ} {ᶜ∇ᶜ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᶜ∇ᶜ} {ᶜ∇ᵇ} {ᶜ∇ᵇ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
   blah {a⌣a′ = ᶜ∇ᶜ} {ᶜ∇ᶜ} {ᶜ∇ᶜ} E⌣E′ E′⌣E″ E⌣E″ = {!!}
--(E⌣E′ ᵇᵇ│ Q) (E′ ᵇ│ᵇ F) (E ᵇ│ᵇ .F) | E′/E ᵀΔ E/E′ | (E″/E ᵇ│ .((push *) Q)) ᵀΔ E/E″ = {!a′⌣a″!}
-}
   blah E⌣E′ E′⌣E″ E⌣E″ = {!!}
{-
   blah _ (E ᵇ│ᶜ F) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E ᶜ│ᵇ F) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E ᶜ│ᶜ F) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ │•ᵇ F) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E′⌣E″ │•ᶜ F) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E₁ ᵇ│• E′⌣E″) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E₁ ᶜ│• E′⌣E″) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E′⌣E″ │ᵥᵇ F) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E′⌣E″ │ᵥᶜ F) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E₁ ᵇ│ᵥ E′⌣E″) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E₁ ᶜ│ᵥ E′⌣E″) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (E′⌣E″ ➕₁ Q) _ | Delta E′/E E/E′₁ | Delta E″/E E/E′ = {!!}
   blah _ (P │ᵇᵇ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (P │ᵇᶜ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (P │ᶜᶜ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ ᵇᵇ│ Q) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ ᵇᶜ│ Q) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ ᶜᶜ│ Q) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ │• E′⌣E″₁) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ │•ᵥ E′⌣E″₁) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (E′⌣E″ │ᵥ E′⌣E″₁) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (ν• E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (ν•ᵇ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (ν•ᶜ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (νᵇᵇ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (νᵛᵛ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (νᵇᶜ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (νᶜᶜ E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
   blah _ (! E′⌣E″) _ | Delta E′/E E/E′ | Delta E″/E E/E′₁ = {!!}
-}
