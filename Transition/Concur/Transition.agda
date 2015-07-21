-- The "residual" of a concurrent pair after a third concurrent transition. See 0.1 release notes.
module Transition.Concur.Transition where

   open import SharedModules

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⌣-sym; ᴬ⊖); open _ᴬ⌣_
   open import Action.Concur.Action using (/-preserves-ᴬ⌣)
   open import Name using (zero)
   open import Proc as ᴾ using (Proc)
   open import Ren as ᴿ using (Ren; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; module Delta′; Delta; ⊖; ⊖₁; ⌣-sym);
      open Concur₁; open Delta′
   open import Transition.Concur.Cofinal using (⊖-✓-⋉)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; module _Δ′_)
   open import Transition.Concur.Ren using (_*ᵇᵇ⌣; _*ᵇᶜ⌣; _*ᶜᵇ⌣; _*ᶜᶜ⌣)

   -- A "cyclic" version is probably more useful. However for the asymmetric version of the relation, 𝐸″
   -- would be mostly uninhabited. TODO: 𝐸/E and E/𝐸 notation, once I've improved overloading situation.
   postulate
      /-preserves-⌣ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
                      {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                      (𝐸 : E ⌣[ 𝑎 ] E′) → E′ ⌣[ 𝑎′ ] E″ → (𝐸″ : E″ ⌣[ 𝑎″ ] E) →
                      E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ 𝑎 𝑎′ (ᴬ⌣-sym 𝑎″) ] E/E′ (⊖ 𝐸″)

      -- This would be the correctness property for E\𝐸, I think.
      /-preserves-cofin :
         ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
         {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
         (𝐸 : E ⌣[ 𝑎 ] E′) (𝐸′ : E′ ⌣[ 𝑎′ ] E″) (𝐸″ : E″ ⌣[ 𝑎″ ] E) →
         let 𝐸′/E = /-preserves-⌣ 𝐸 𝐸′ 𝐸″; 𝐸/E″ = /-preserves-⌣ 𝐸″ 𝐸 𝐸′; open _Δ′_
         in E/E′ (⊖ 𝐸′/E) ≅ E/γ (⊖′[ 𝑎″ , zero ] (E′/E (⊖ 𝐸/E″)) (⊖-✓-⋉ 𝐸″))

   -- The residual 𝐸′/E. Slight case-explosion because of need to distinguish the ˣ∇ˣ and ᵇ∇ᵇ cases pairwise.
   /-preserves-⌣₁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a ᴬ⌣ a″}
                   {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                   (𝐸 : E ⌣₁[ 𝑎 ] E′) → E′ ⌣₁[ 𝑎′ ] E″ → (𝐸″ : E ⌣₁[ 𝑎″ ] E″) →
                   E′/E (⊖₁ 𝐸) ⌣₁[ /-preserves-ᴬ⌣ 𝑎 𝑎′ 𝑎″ ] E′/E (⊖₁ 𝐸″)
   /-preserves-⌣₁ (𝐸 │ᵥ• 𝐹) (𝐸′ │• 𝐹′) (𝐸″ │ᵥ• 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ•_ {y = y} 𝐸 𝐹) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │ᵥ′ 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ•_ {y = y} 𝐸 𝐹) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │ᵥ 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)

   /-preserves-⌣₁ (_│•ᵥ_ {y = y} 𝐸 𝐹) (𝐸′ │ᵥ• 𝐹′) (𝐸″ │• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = ((pop y) *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (𝐸 │•ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (𝐸 │•ᵥ 𝐹) (𝐸′ │ᵥ′ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = ?

   /-preserves-⌣₁ (_│ᵥᵇ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣₁ (𝐸 │ᵥᵇ F) (𝐸′ │ᵥ 𝐹) (𝐸″ │ᵥᵇ F′) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ (push *ᵇᵇ⌣) 𝐹

   /-preserves-⌣₁ (_│ᵥᶜ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ• 𝐹′
   /-preserves-⌣₁ (𝐸 │ᵥᶜ F) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥᶜ F′) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ 𝐹′

   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) (𝐸 │ᵥ′ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │ᵥ′ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) (𝐸 │ᵥ′ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E′ 𝐹″) = ? -- (push *ᵇᵇ⌣) 𝐸 │ᵥ• (/-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) (𝐸 │ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) (𝐸 │ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) (𝐸 │ᵥ′ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E′ 𝐹″) = ? -- (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) (𝐸 │ᵥ′ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E′ 𝐹″) = ? -- (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) (𝐸 │ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) (𝐸 │ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᶜ│ᵥ 𝐹) (𝐸 │ᵥ• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸 │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᶜ│ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᶜ│ᵥ 𝐹) _ (E′ │ᵛᵛ 𝐹″) = ?

   /-preserves-⌣₁ (𝐸 │ᵥ′ 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ′ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥ′ 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ′ 𝐹) (𝐸′ │ᵥ′ 𝐹′) (𝐸″ │ᵥ 𝐹″) = ? -- νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ 𝐹) (𝐸′ │ᵥ′ 𝐹′) (𝐸″ │ᵥ′ 𝐹″) = ? -- νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ′ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥ 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ 𝐹) (𝐸′ │ᵥ′ 𝐹′) (𝐸″ │ᵥ 𝐹″) = ? -- νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥ′ 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥ 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (𝐸 │ᵥ′ 𝐹) (𝐸′ │ᵥ′ 𝐹′) (𝐸″ │ᵥ′ 𝐹″) = ?

   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᵇ F) (E ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᶜ F) (E ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵛᵛ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q

   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᶜ│• 𝐹″) = E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (E ᵇ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᵇᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵛᵛ 𝐹″) = ? -- P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {𝑎 = ᵇ∇ᵇ} 𝐸″ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {𝑎 = ˣ∇ˣ} 𝐸″ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᵛᵛ│ .Q) (𝐸″ ᵇᶜ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} .P 𝐹″) = (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} .P 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} .E 𝐹″) = (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} .E 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᵛᵛ 𝐹′) (.P │ᵇᶜ 𝐹″) = ? -- (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᵛᵛ│ .Q) = ?
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᵛᵛ│ .Q) (𝐸″ ᶜᶜ│ .Q) = ?
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᵛᵛ│ .Q) (𝐸″ ᵛᵛ│ .Q) = ?

   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ ᶜᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ Q
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) = ? -- E′/E (⊖₁ 𝐸) ᶜ│ᵇ F
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) = ? -- E′/E (⊖₁ 𝐸) ᶜ│ᶜ F
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ │•ᶜ F) (𝐸″ │•ᶜ .F) = ? -- (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
--    ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ F
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᶜ .F) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ ᵛᵛ│ .Q) (𝐸″ ᶜᶜ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᵛᵛ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q
   /-preserves-⌣₁ (𝐸 ᵛᵛ│ Q) (𝐸′ ᵛᵛ│ .Q) (𝐸″ ᵛᵛ│ .Q) = ? -- /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q

   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᶜ│• 𝐹″) = _ ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᵛᵛ 𝐹″) = ?
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᵛᵛ 𝐹′) (.P │ᶜᶜ 𝐹″) = ?
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᵛᵛ 𝐹′) (.P │ᵛᵛ 𝐹″) = ?

   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (.P │ᶜᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = ? -- P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (E ᶜ│• 𝐹′) (.E ᶜ│• 𝐹″) = ? -- _ ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (E ᶜ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = ? -- E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = ? -- P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (.P │ᵛᵛ 𝐹′) (.P │ᶜᶜ 𝐹″) = ? -- P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᵛᵛ 𝐹″) = ? -- P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵛᵛ 𝐹) (.P │ᵛᵛ 𝐹′) (.P │ᵛᵛ 𝐹″) = ? -- P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᵇ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᵇ│• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣₁ (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ {𝑎′ = ᵇ∇ᵇ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ {𝑎′ = ˣ∇ˣ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᵇ F) (P │ᵇᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ (push *ᵇᶜ⌣) 𝐹

   /-preserves-⌣₁ (E ᵇ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᶜᵇ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (E′ ᶜ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• (push *ᶜᶜ⌣) 𝐹′
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (P │ᶜᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ (push *ᶜᶜ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (P │ᵛᵛ 𝐹) (.E ᵇ│ᶜ F′) = ? -- _ │ᶜᶜ (push *ᶜᶜ⌣) 𝐹

   /-preserves-⌣₁ (E ᶜ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᶜ_ {y = y} {a = a} 𝐸″ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = E′/E (⊖₁ 𝐸″) ᵇ│• 𝐹′
   /-preserves-⌣₁ (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ 𝐹
   /-preserves-⌣₁ {𝑎′ = ˣ∇ˣ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣₁ {𝑎′ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᵇ F) (P │ᵇᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ 𝐹′

   /-preserves-⌣₁ (E ᶜ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᶜᵇ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (E′ ᶜ│• 𝐹) (_│•ᶜ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (P │ᶜᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᶜᶜ 𝐹′
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (P │ᵛᵛ 𝐹′) (.E ᶜ│ᶜ F′) = ? -- _ │ᶜᶜ 𝐹′

   /-preserves-⌣₁ (𝐸 ➕₁ Q) (𝐸′ ➕₁ .Q) (𝐸″ ➕₁ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᵇ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᵇ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᵇ (push *ᵇ) F
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵇ (push *ᶜ) F
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (𝐸″ │•ᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ᵇ∇ᵇ} {𝑎″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ᵇ∇ᵇ} {𝑎″ = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ˣ∇ˣ} {𝑎″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ˣ∇ˣ} {𝑎″ = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {ᵇ∇ᵇ} {ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {ˣ∇ˣ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {ˣ∇ˣ} {ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ᵇ∇ᵇ} {𝑎″ = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} {𝑎′ = ˣ∇ˣ} {𝑎″ = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {𝑎′ = ᵇ∇ᵇ} {𝑎″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {𝑎′ = ᵇ∇ᵇ} {𝑎″ = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {𝑎′ = ˣ∇ˣ} {𝑎″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} {𝑎′ = ˣ∇ˣ} {𝑎″ = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {𝑎 = ˣ∇ˣ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) (𝐸′ │• 𝐹) (_│•ᵇ_ {y = z} {a = .a} 𝐸″ F′)
      with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸)) | (pop z *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E′ | pop-y*E/E″ rewrite pop∘push y a | pop∘push z a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• (push *ᶜᶜ⌣) 𝐹
   /-preserves-⌣₁ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) (𝐸′ │•ᵥ 𝐹) (𝐸″ │ᵥᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ (push *ᶜᵇ⌣) 𝐹

   /-preserves-⌣₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) (_│•_ {x = x} {.y} {u} {z} 𝐸′ 𝐹) (𝐸″ │•ᶜ F′)
      with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸)) | (pop y *ᵇ) (E′/E (⊖₁ 𝐸′)) | (pop z *ᵇ) (E/E′ (⊖₁ 𝐸′)) | (pop z *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E′ | pop-y*E″/E′ | pop-z*E′/E″ | pop-z*E/E″
      rewrite pop∘push y a | pop∘push u y | pop∘push x z | pop∘push z a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• 𝐹
   /-preserves-⌣₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │ᵥᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ 𝐹′

   /-preserves-⌣₁ (E ᵇ│• 𝐹) (𝐸 │• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᶜ│• 𝐹) (𝐸′ │• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸′ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᶜ│• 𝐹) (𝐸′ │•ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 │• 𝐹) (𝐸′ │• 𝐹′) (𝐸″ │• 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (𝐸 │• 𝐹) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (ν• 𝐸) (ν• 𝐸′) (ν• 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν• 𝐸) (ν•ᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν• 𝐸) (ν•ᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νᵇᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νˣˣ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νᵇᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (ν•ᶜ 𝐸) (νᶜᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᶜ 𝐸) (νᵛᵛ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᶜ 𝐸) (νᶜᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᵇ_ {a′ = a′} 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push x | swap∘push∘push a | swap∘push∘push a′ =
      νᵇᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νˣˣ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νˣˣ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} 𝐸) (νˣˣ 𝐸′) (νᵇᵇ 𝐸″) = νˣˣ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} 𝐸) (νˣˣ 𝐸′) (νᵇᵇ 𝐸″) = νˣˣ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ 𝐸) (νˣˣ 𝐸′) (νˣˣ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a | swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {u •} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {• u} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E

   /-preserves-⌣₁ (νˣˣ 𝐸) (νˣˣ 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νˣˣ 𝐸) (νˣˣ 𝐸′) (νˣˣ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νˣˣ 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νˣˣ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = x •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νˣˣ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • x} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νˣˣ 𝐸) (νᵇᵇ 𝐸′) (νˣˣ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)

   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᶜ 𝐸′) (νᵇᶜ_ {a′ = a″} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ | swap∘push∘push a″ = νᶜᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᶜ 𝐸) (νᵛᵛ 𝐸′) (νᵇᶜ 𝐸″) = ?
   /-preserves-⌣₁ (νᵇᶜ 𝐸) (νᶜᵇ_ {a = a} {a′} 𝐸′) (νᵇᵇ_ {a = x •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a | swap∘push∘push a′ =
      νᶜᵇ swap*E′/𝐸″/E

   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵇᵇ_ {a = • x} {u •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵇᵇ_ {a = • x} {• u} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νˣˣ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E

   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νᵇᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νᵇᵇ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νˣˣ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νˣˣ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νᵇᶜ 𝐸′) (νᶜᶜ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | swap*E/E′ rewrite swap∘push∘push a = νᵇᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᵇ 𝐸) (νᵇᶜ 𝐸′) (νᵛᵛ 𝐸″) = ?

   /-preserves-⌣₁ (νᶜᶜ 𝐸) (νᶜᶜ 𝐸′) (νᶜᶜ 𝐸″) = νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᶜ 𝐸) (νᶜᶜ 𝐸′) (νᵛᵛ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᶜ 𝐸) (νᵛᵛ 𝐸′) (νᶜᶜ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᶜ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᶜᶜ 𝐸′) (νᶜᶜ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᶜᶜ 𝐸′) (νᵛᵛ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᶜᶜ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = ? -- νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᶜ_ {a = a} 𝐸) (νᶜᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E″ rewrite swap∘push∘push a = νᶜᵇ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᶜᵇ 𝐸′) (νᶜᵇ 𝐸″) = ?

   /-preserves-⌣₁ (! 𝐸) (! 𝐸′) (! 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
