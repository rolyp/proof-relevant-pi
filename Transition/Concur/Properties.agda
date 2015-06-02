module Transition.Concur.Properties where

   open import SharedModules

   open import Action as ᴬ using (Action; _ᴬ⌣_); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ._ᴬ⌣_
   open import Proc as ᴾ using (Proc)
   open import Ren as ᴿ using (Ren; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
   open import Transition.Concur using (Concur₁; module Concur₁; Concur; Delta′; module Delta′; Delta; ⊖₁; ⌣-sym);
      open Concur₁; open Delta′
   open import Transition.Concur.Ren using (/-preserves-ᴬ⌣; _*ᵇᵇ⌣; _*ᵇᶜ⌣; _*ᶜᵇ⌣; _*ᶜᶜ⌣)

   -- Residuation preserves concurrency. There is an unpleasant case-explosion here because of the need to
   -- distinguish the ᵛ∇ᵛ and ᵇ∇ᵇ cases pairwise across the three transitions.

   /-preserves-⌣ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                   {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                   (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → E′ ⌣₁[ a′⌣a″ ] E″ → (E⌣E″ : E ⌣₁[ a⌣a″ ] E″) →
                   E′/E (⊖₁ E⌣E′) ⌣₁[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ a⌣a″ ] E′/E (⊖₁ E⌣E″)
{-
   /-preserves-⌣ {E = x •∙ ._} E⌣E′ () E⌣E″
   /-preserves-⌣ {E = • x 〈 y 〉∙ ._} E⌣E′ () E⌣E″
   /-preserves-⌣ (E⌣E′ ➕₁ Q) (E′⌣E″ ➕₁ .Q) (E⌣E″ ➕₁ .Q) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᵇ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᵇ│ᶜ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) = E′/E (⊖₁ E⌣E′) ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) = E′/E (⊖₁ E⌣E′) ᶜ│ᵇ F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) = E′/E (⊖₁ E⌣E′) ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) = E′/E (⊖₁ E⌣E′) ᶜ│ᶜ F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │•ᵇ F) (_│•ᵇ_ {y = y} {a = a} E⌣E″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᵇ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │•ᵇ F) (E⌣E″ │•ᵇ .F) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │•ᶜ F) (_│•ᵇ_ {y = y} {a = a} E⌣E″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│• F′⌣F″) (_│•ᵇ_ {y = y} {a = a} E⌣E′ F′) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ E⌣E′) ᵇ│• (push *ᵇᶜ⌣) F′⌣F″
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│• F′⌣F″) (_│•ᵇ_ {y = y} {a = a} E⌣E′ F′) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ E⌣E′) ᶜ│• (push *ᶜᶜ⌣) F′⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │ᵥᵇ F) (E⌣E″ │ᵥᵇ .F) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ │ᵥᵇ F) (E⌣E″ │ᵥᵇ .F) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᵇ .F) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ F⌣F′) (E⌣E′ │ᵥᵇ F′) = E′/E (⊖₁ E⌣E′) ᵇ│ᵥ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ F⌣F′) (E⌣E′ │ᵥᵇ F′) = E′/E (⊖₁ E⌣E′) ᶜ│ᵥ (push *ᶜᵇ⌣) F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᵇ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᵇ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᵇ F) (P │ᵇᶜ F⌣F′) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ (push *ᵇᶜ⌣) F⌣F′
   /-preserves-⌣ (E ᵇ│ᶜ F) (P │ᶜᶜ F⌣F′) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ (push *ᶜᶜ⌣) F⌣F′
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᵇ│ .Q) (E⌣E″ ᵇᵇ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (E⌣E′ ᵇᵇ│ Q) (E′⌣E″ ᵇᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ (E⌣E′ ᵇᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᵇᶜ│ .Q) =
      /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) (E′⌣E″ │• F⌣F′) (_│•ᵇ_ {y = z} {a = .a} E⌣E″ F′)
      with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E′)) | (pop z *ᵇ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E′ | pop-y*E/E″ rewrite pop∘push y a | pop∘push z a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │• (push *ᶜᶜ⌣) F⌣F′
   /-preserves-⌣ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) (E′⌣E″ │•ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᵥ (push *ᶜᵇ⌣) F⌣F′
   /-preserves-⌣ (E⌣E′ │ᵥᵇ F) (E′⌣E″ │ᵥ F⌣F′) (E⌣E″ │ᵥᵇ F′) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥ (push *ᵇᵇ⌣) F⌣F′
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │•ᶜ F) (_│•ᶜ_ {y = y} {a = a} E⌣E″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᶜ F
   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│• F′⌣F″) (_│•ᶜ_ {y = y} {a = a} E⌣E″ F′) with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E″ rewrite pop∘push y a = E′/E (⊖₁ E⌣E″) ᵇ│• F′⌣F″
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│• F⌣F′) (_│•ᶜ_ {y = y} {a = a} E⌣E′ F′) with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ E⌣E′) ᶜ│• F⌣F′
-}
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ │ᵥᶜ F) (E⌣E″ │ᵥᶜ .F) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥᶜ F
   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ F⌣F′) (E⌣E′ │ᵥᶜ F′) = E′/E (⊖₁ E⌣E′) ᵇ│ᵥ F⌣F′
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ F⌣F′) (E⌣E′ │ᵥᶜ F′) = E′/E (⊖₁ E⌣E′) ᶜ│ᵥ F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ F⌣F′) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ F⌣F′
   /-preserves-⌣ (E ᶜ│ᵇ F) (P │ᵇᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ F′⌣F″
   /-preserves-⌣ (E ᶜ│ᶜ F) (P │ᶜᶜ F′⌣F″) (.E ᶜ│ᶜ F′) = _ │ᶜᶜ F′⌣F″
   /-preserves-⌣ (E⌣E′ ᶜᶜ│ Q) (E′⌣E″ ᶜᶜ│ .Q) (E⌣E″ ᶜᶜ│ .Q) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ ᶜᶜ│ Q
   /-preserves-⌣ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) (_│•_ {x = x} {.y} {u} {z} E′⌣E″ F⌣F′) (E⌣E″ │•ᶜ F′)
      with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E′)) | (pop y *ᵇ) (E′/E (⊖₁ E′⌣E″)) |
           (pop z *ᵇ) (E/E′ (⊖₁ E′⌣E″)) | (pop z *ᶜ) (E/E′ (⊖₁ E⌣E″))
   ... | pop-y*E/E′ | pop-y*E″/E′ | pop-z*E′/E″ | pop-z*E/E″
      rewrite pop∘push y a | pop∘push u y | pop∘push x z | pop∘push z a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │• F⌣F′
   /-preserves-⌣ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᵥ F′⌣F″
   /-preserves-⌣ (E⌣E′ │ᵥᶜ F) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │ᵥᶜ F′) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥ F′⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (E ᵇ│• F′⌣F″) (.E ᵇ│• F⌣F″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (E ᵇ│• F′⌣F″) (.E ᵇ│• F⌣F″) = (push *ᵇ) E ᵇ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᵇ│• F⌣F″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E F⌣F″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E F⌣F″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E F⌣F″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E F⌣F″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E F⌣F″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E F⌣F″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E F⌣F″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E F⌣F″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E F⌣F″) = (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E F⌣F″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) =
      (push *) P │ᵇᵇ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) =
      (push *) P │ᵇᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) =
      (push *) P │ᵇᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with ⊖₁ F⌣F′ | ⊖₁ F⌣F″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F ᵀΔ F/F′ | F″/F ᵀΔ F/F″ | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) =
      (push *) P │ᶜᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″)
      with ⊖₁ F⌣F′ | ⊖₁ F⌣F″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F ᵀΔ F/F′ | F″/F ᵀΔ F/F″ | F′/F⌣F″/F = {!!}
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᵇ F′⌣F″) (.P │ᵇᵇ F⌣F″) =
      (push *) P │ᶜᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ F⌣F′) (.P │ᵇᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) = (push *) P │ᵇᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ F⌣F′) (.P │ᵇᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) = (push *) P │ᶜᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᵇᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᵇᶜ F⌣F″) = (push *) P │ᶜᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │• F′⌣F″) (E′ ᵇ│• F⌣F″) = (push *ᵇᵇ⌣) E⌣E′ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │•ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᵇ│• F⌣F′) (E⌣E′ │•ᵥ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″)
      with /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | F′/F⌣F″/F = {!!}
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F′⌣F″) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ F⌣F″) =
      (push *ᵇᵇ⌣) E⌣E′ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (E ᶜ│• F′⌣F″) (.E ᶜ│• F⌣F″) = _ ᶜ│• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (E ᶜ│ᵥ F′⌣F″) (.E ᶜ│ᵥ F⌣F″) = E ᶜ│ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (P │ᶜᶜ F⌣F′) (.P │ᶜᶜ F′⌣F″) (.P │ᶜᶜ F⌣F″) = P │ᶜᶜ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᶜ│• F⌣F′) (E′⌣E″ │• F′⌣F″) (E′ ᶜ│• F⌣F″) = E′⌣E″ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᶜ│• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) = E′⌣E″ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E ᶜ│ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E′ ᶜ│ᵥ F⌣F″) = E′⌣E″ │ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E⌣E′ │• F⌣F′) (E′⌣E″ │• F′⌣F″) (E⌣E″ │• F⌣F″) =
      (pop _ *ᵇᵇ⌣) (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″) │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E⌣E′ │• F⌣F′) (E′⌣E″ │•ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″) =
      (pop _ *ᵇᵇ⌣) (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″) │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (E⌣E′ │•ᵥ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (E⌣E″ │•ᵥ F⌣F″) =
      (pop _ *ᵇᵇ⌣) (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″) │ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) (E′⌣E″ │ᵥ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″) =
      νᶜᶜ (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ {!!}
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″) =
      νᶜᶜ (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″)
      with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ | /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″
   ... | E′/E⌣E″/E | F′/F⌣F″/F = νᶜᶜ {!!}
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″) =
      νᶜᶜ (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E″ F⌣F″) =
      νᶜᶜ (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │•ᵥ /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E′⌣E″ F′⌣F″) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E″ F⌣F″) =
      νᶜᶜ (/-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″ │• /-preserves-⌣ F⌣F′ F′⌣F″ F⌣F″)
   /-preserves-⌣ (ν• E⌣E′) (ν• E′⌣E″) (ν• E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν• E⌣E′) (ν•ᵇ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν• E⌣E′) (ν•ᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵇᵇ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵛᵛ E′⌣E″) (ν•ᵇ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᵇ E⌣E′) (νᵇᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   /-preserves-⌣ (ν•ᶜ E⌣E′) (νᶜᶜ E′⌣E″) (ν•ᶜ E⌣E″) = /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
{-
   /-preserves-⌣ (νᵇᵇ_ {a = x •} {a} E⌣E′) (νᵇᵇ_ {a′ = a′} E′⌣E″) (νᵇᵇ E⌣E″)
      with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᵇ) E′/E | (swap *ᵇ) E″/E | (swap *ᵇᵇ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push x | swap∘push∘push a | swap∘push∘push a′ =
      νᵇᵇ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = • y} E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᵇ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = • y} E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᵇ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = y •} E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᵇ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = y •} E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᵇ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} E⌣E′) (νᵇᵇ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᶜ (swap *ᵇᶜ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} E⌣E′) (νᵇᵇ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᶜ (swap *ᵇᶜ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = x •} E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᶜ) E′/E | (swap *ᵇ) E″/E | (swap *ᶜᵇ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᵇ E′⌣E″) (νᵇᵇ_ {a′ = • x} E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᶜ) E′/E | (swap *ᵇ) E″/E | (swap *ᶜᵇ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᵇ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ (swap *ᶜᶜ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = x •} E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵛᵛ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵛᵛ (swap *ᵇᵇ⌣) E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ E⌣E′) (νᵛᵛ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᵇᶜ ((swap *ᵇᶜ⌣) E′/E⌣E″/E)
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵛᵛ E′⌣E″) (νᵇᵇ E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᶜ) E′/E | (swap *ᵇ) E″/E | (swap *ᶜᵇ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E = {!!}
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵛᵛ E′⌣E″) (νᵛᵛ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ ((swap *ᶜᶜ⌣) E′/E⌣E″/E)
   /-preserves-⌣ (νᵇᵇ_ {a = x •} {a} E⌣E′) (νᵇᶜ_ {a′ = a′} E′⌣E″) (νᵇᶜ E⌣E″)
       with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᵇ) E′/E | (swap *ᶜ) E″/E | (swap *ᵇᶜ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push a | swap∘push∘push a′ = νᵇᶜ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {u •} E⌣E′) (νᵇᶜ_ {a′ = a′} E′⌣E″) (νᵇᶜ E⌣E″)
      with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᵇ) E′/E | (swap *ᶜ) E″/E | (swap *ᵇᶜ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {• u} E⌣E′) (νᵇᶜ_ {a′ = a′} E′⌣E″) (νᵇᶜ E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᵇ) E′/E | (swap *ᶜ) E″/E | (swap *ᵇᶜ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᵛᵛ E⌣E′) (νᵇᶜ_ {a′ = a′} E′⌣E″) (νᵇᶜ E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᶜ) E′/E | (swap *ᶜ) E″/E | (swap *ᶜᶜ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᵇᶜ_ {a′ = a′} E⌣E′) (νᶜᶜ E′⌣E″) (νᵇᶜ_ {a′ = a″} E⌣E″) with ⊖₁ E⌣E′ | ⊖₁ E⌣E″ | /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E ᵀΔ _ | E″/E ᵀΔ _ | E′/E⌣E″/E with (swap *ᶜ) E′/E | (swap *ᶜ) E″/E | (swap *ᶜᶜ⌣) E′/E⌣E″/E
   ... | swap*E′/E | swap*E″/E | swap*E′/E⌣E″/E rewrite swap∘push∘push a′ | swap∘push∘push a″ = νᶜᶜ swap*E′/E⌣E″/E
   /-preserves-⌣ (νᶜᶜ E⌣E′) (νᶜᶜ E′⌣E″) (νᶜᶜ E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = νᶜᶜ E′/E⌣E″/E
   /-preserves-⌣ (! E⌣E′) (! E′⌣E″) (! E⌣E″) with /-preserves-⌣ E⌣E′ E′⌣E″ E⌣E″
   ... | E′/E⌣E″/E = E′/E⌣E″/E
-}
   /-preserves-⌣ _ _ _ = {!!}
