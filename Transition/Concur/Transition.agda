-- The "residual" of a concurrent pair after a third concurrent transition. There is a slight case-explosion here
-- because of the need to distinguish the ᵛ∇ᵛ and ᵇ∇ᵇ cases pairwise across the three transitions.
-- Haven't found a way to prove this for the symmetrised relation ⌣ as defined. Can prove it for a version of ⌣
-- which has a symmetric variant of each rule, but the proof is big and Agda runs out of memory compiling it.
module Transition.Concur.Transition where

   open import SharedModules

   open import Action as ᴬ using (Action; _ᴬ⌣_; ᴬ⌣-sym); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ._ᴬ⌣_
   open import Proc as ᴾ using (Proc)
   open import Ren as ᴿ using (Ren; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; module Delta′; Delta; ⊖; ⊖₁; ⌣-sym);
      open Concur₁; open Delta′
   open import Transition.Concur.Ren using (/-preserves-ᴬ⌣; _*ᵇᵇ⌣; _*ᵇᶜ⌣; _*ᶜᵇ⌣; _*ᶜᶜ⌣)

   -- A "rotationally symmetric" version might be more useful.
   postulate
      /-preserves-⌣₁′ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {𝑎 : a ᴬ⌣ a′} {𝑎′ : a′ ᴬ⌣ a″} {𝑎″ : a″ ᴬ⌣ a}
                       {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                       (𝐸 : E ⌣₁[ 𝑎 ] E′) → E′ ⌣₁[ 𝑎′ ] E″ → (𝐸″ : E″ ⌣₁[ 𝑎″ ] E) →
                       E′/E (⊖₁ 𝐸) ⌣₁[ /-preserves-ᴬ⌣ 𝑎 𝑎′ (ᴬ⌣-sym 𝑎″) ] E/E′ (⊖₁ 𝐸″)

   -- The residual 𝐸′/E.
   /-preserves-⌣₁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                   {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                   (𝐸 : E ⌣₁[ a⌣a′ ] E′) → E′ ⌣₁[ a′⌣a″ ] E″ → (𝐸″ : E ⌣₁[ a⌣a″ ] E″) →
                   E′/E (⊖₁ 𝐸) ⌣₁[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ a⌣a″ ] E′/E (⊖₁ 𝐸″)
   /-preserves-⌣₁ (𝐸 │ᵥ• 𝐹) (𝐸′ │• 𝐹′) (𝐸″ │ᵥ• 𝐹″) = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ•_ {y = y} 𝐸 𝐹) (𝐸′ │•ᵥ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ•_ {y = y} 𝐸 𝐹) (𝐸′ │•ᵥ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)

   /-preserves-⌣₁ (_│•ᵥ_ {y = y} 𝐸 𝐹) (𝐸′ │ᵥ• 𝐹′) (𝐸″ │• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ = ((pop y) *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (𝐸 │•ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (_│ᵥᵇ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣₁ (𝐸 │ᵥᵇ F) (𝐸′ │ᵥ 𝐹) (𝐸″ │ᵥᵇ F′) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ (push *ᵇᵇ⌣) 𝐹

   /-preserves-⌣₁ (_│ᵥᶜ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │ᵥ• 𝐹′
   /-preserves-⌣₁ (𝐸 │ᵥᶜ F) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥᶜ F′) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ 𝐹′

   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ• (/-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᶜ│ᵥ 𝐹) (𝐸 │ᵥ• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸 │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᶜ│ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (𝐸′ │ᵥ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″)

   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᵇ F) (E ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᶜ F) (E ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q

   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᶜ│• 𝐹″) = E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (E ᵇ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᵇᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣₁ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} .P 𝐹″) = (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} .P 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) = (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᵇᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ Q
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F
   /-preserves-⌣₁ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q

   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᶜ│• 𝐹″) = _ ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (P │ᶜᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᵇ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᵇ│• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣₁ (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ {a′⌣a″ = ᵇ∇ᵇ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ {a′⌣a″ = ᵛ∇ᵛ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᵇ F) (P │ᵇᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ (push *ᵇᶜ⌣) 𝐹

   /-preserves-⌣₁ (E ᵇ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᶜᵇ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (E′ ᶜ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• (push *ᶜᶜ⌣) 𝐹′
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣₁ (E ᵇ│ᶜ F) (P │ᶜᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ (push *ᶜᶜ⌣) 𝐹

   /-preserves-⌣₁ (E ᶜ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᶜ_ {y = y} {a = a} 𝐸″ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = E′/E (⊖₁ 𝐸″) ᵇ│• 𝐹′
   /-preserves-⌣₁ (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ 𝐹
   /-preserves-⌣₁ {a′⌣a″ = ᵛ∇ᵛ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣₁ {a′⌣a″ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᵇ F) (P │ᵇᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ 𝐹′

   /-preserves-⌣₁ (E ᶜ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᶜᵇ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (E′ ᶜ│• 𝐹) (_│•ᶜ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ 𝐹
   /-preserves-⌣₁ (E ᶜ│ᶜ F) (P │ᶜᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᶜᶜ 𝐹′

   /-preserves-⌣₁ (𝐸 ➕₁ Q) (𝐸′ ➕₁ .Q) (𝐸″ ➕₁ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᵇ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᵇ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᵇ (push *ᵇ) F
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᵇ (push *ᶜ) F
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (𝐸″ │•ᵇ .F) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᵇᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

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
   /-preserves-⌣₁ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (E ᶜ│• 𝐹) (𝐸′ │• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸′ │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (E ᶜ│• 𝐹) (𝐸′ │•ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (𝐸 │• 𝐹) (𝐸′ │• 𝐹′) (𝐸″ │• 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │• /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣₁ (𝐸 │• 𝐹) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″) │•ᵥ /-preserves-⌣₁ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣₁ (ν• 𝐸) (ν• 𝐸′) (ν• 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν• 𝐸) (ν•ᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν• 𝐸) (ν•ᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νᵇᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νᵛᵛ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᵇ 𝐸) (νᵇᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (ν•ᶜ 𝐸) (νᶜᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (ν•ᶜ 𝐸) (νᶜᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᵇ_ {a′ = a′} 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push x | swap∘push∘push a | swap∘push∘push a′ =
      νᵇᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″) = νᵛᵛ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″) = νᵛᵛ (swap *ᵇᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a | swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {u •} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵇᵇ_ {a = • x} {• u} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E

   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = x •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • x} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣₁ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)

   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᶜ 𝐸′) (νᵇᶜ_ {a′ = a″} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ | swap∘push∘push a″ = νᶜᶜ swap*E′/𝐸″/E
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
   /-preserves-⌣₁ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵛᵛ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᶜ⌣) (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E

   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νᵇᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νᵇᵇ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νᵛᵛ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νᵛᵛ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᵇ_ {a = a} 𝐸) (νᵇᶜ 𝐸′) (νᶜᶜ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | swap*E/E′ rewrite swap∘push∘push a = νᵇᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣₁ (νᶜᶜ 𝐸) (νᶜᶜ 𝐸′) (νᶜᶜ 𝐸″) = νᶜᶜ /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣₁ (νᶜᶜ_ {a = a} 𝐸) (νᶜᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E″ rewrite swap∘push∘push a = νᶜᵇ (/-preserves-⌣₁ 𝐸 𝐸′ 𝐸″)

   /-preserves-⌣₁ (! 𝐸) (! 𝐸′) (! 𝐸″) = /-preserves-⌣₁ 𝐸 𝐸′ 𝐸″
