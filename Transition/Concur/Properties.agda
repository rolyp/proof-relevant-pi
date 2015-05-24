module Transition.Concur.Properties where

   open import SharedModules

   open import Data.Fin using (Fin; toℕ)

   open import Action as ᴬ using (Action; inc; _ᴬ⌣_; module _ᴬ⌣_); open ᴬ.Actionᵇ; open _ᴬ⌣_
   import Action.Ren
   open import Name using (_+_; zero)
   open import Proc using (Proc)
   import Proc.Ren
   open import StructuralCong.Proc using (_≈_; module _≈_; ≈-refl; ≈-reflexive; ≈-sym; _*⁼);
      open _≈_ renaming (trans to ≈-trans)
   open import Ren as ᴿ using (Ren; ᴺren; suc; pop; push; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; blah₂; Delta′; Delta; module Delta′; ᴬ⊖; ᴬ⊖-✓; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- structurally congruent, or structurally congruent with each other's swap image.
   cofinal : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) →
             let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ a⌣a′)) in Proc Γ′ → Proc Γ′ → Set
   cofinal ᵛ∇ᵛ = _≈_
   cofinal ᵇ∇ᵇ P₁ P₂ = P₁ ≈ (swap *) P₂
   cofinal ᵇ∇ᶜ = _≈_
   cofinal ᶜ∇ᵇ = _≈_
   cofinal ᶜ∇ᶜ = _≈_

   -- Correctness of residuals, with respect to the above notion of cofinality. TODO: feels wrong to have
   -- the a ᴬ⌣ a′ index on E ⌣ E′, but not to relate it to the one in E Δ E′.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → let open Delta′ (⊖₁ E⌣E′) in cofinal a⌣a′ S S′
   ⊖₁-✓ (E ᵇ│ᵇ F) rewrite swap∘suc-push (target E) | swap∘push (target F) = ≈-refl
   ⊖₁-✓ (E ᵇ│ᶜ F) = ≈-refl
   ⊖₁-✓ (E ᶜ│ᵇ F) = ≈-refl
   ⊖₁-✓ (E ᶜ│ᶜ F) = ≈-refl
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ E/E′ | swap*P′ with (pop y *ᵇ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a | pop∘swap y (target E/E′) = (pop ((push *) y) *⁼) swap*P′ │ ≈-refl
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ E/E′ | P′ with (pop y *ᶜ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a = (pop y *⁼) P′ │ ≈-refl
   ⊖₁-✓ (_ᵇ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ rewrite pop∘suc-push y (target E) = ≈-refl │ Q′
   ⊖₁-✓ (E ᶜ│• F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (E⌣E′ │ᵥᵇ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | swap*P′ rewrite swap∘push (target F) = ν (swap*P′ │ ≈-refl)
   ⊖₁-✓ (E⌣E′ │ᵥᶜ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = ν (P′ │ ≈-refl)
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ with (push *ᵇ) E
   ... | push*E rewrite pop-zero∘suc-push (target E) = ≈-refl │ Q′
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | swap*Q′ rewrite swap∘push (target E) = ν (≈-refl │ swap*Q′)
   ⊖₁-✓ (E ᶜ│ᵥ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ν (≈-refl │ Q′)
   ⊖₁-✓ (P │ᵇᵇ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = {!!} -- ≈-refl │ Q′
   -- ... | _ ᵀΔ[ ᵇ∇ᵇ ] _ | swap*Q′ rewrite swap∘push∘push P = ≈-refl │ swap*Q′
   ⊖₁-✓ (P │ᵇᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (P │ᶜᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (E⌣E′ ᵇᵇ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = {!!} -- P′ │ ≈-refl
   -- ... | _ Δ[ ᵇ∇ᵇ ] _ | swap*P′ rewrite swap∘push∘push Q = swap*P′ │ ≈-refl
   ⊖₁-✓ (E⌣E′ ᵇᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′ │ ≈-refl
   ⊖₁-✓ (E⌣E′ ᶜᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′ │ ≈-refl
   ⊖₁-✓ (E⌣E′ ➕₁ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′
   ⊖₁-✓ (_│•_ {x = x} {y} {u} {z} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | _ ᵀΔ _ | swap*P′ | Q′ with (pop y *ᵇ) E′/E | (pop z *ᵇ) E/E′
   ... | pop-y*E′/E | pop-z*E/E′ rewrite pop∘push u y | pop∘push x z | sym (pop-pop-swap z y (target E/E′)) =
      (pop z *⁼ ∘ suc (pop y) *⁼) swap*P′ │ Q′
   ⊖₁-✓ (_│•ᵥ_ {u = u} {y} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ _ | _ ᵀΔ _ | swap*P′ | Q′ with (pop y *ᵇ) E′/E
   ... | pop-y*E′/E rewrite pop∘push u y =
      ν (≈-trans ((suc (pop y) *⁼) swap*P′) (≈-reflexive (suc-pop∘swap y _)) │ Q′)
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | _ ᵀΔ _ | swap*P′ | Q′ =
      {!!} -- ν (≈-trans ((pop zero *⁼) swap*P′) (≈-reflexive (pop-swap _)) │ Q′)
   -- ... | E′/E ᵀΔ E/E′ | F′/F ᵀΔ F/F′ | swap*P′ | swap*Q′ =
   --    ≈-trans (ν (ν (swap*P′ │ swap*Q′))) (νν-swapₗ _)
   ⊖₁-✓ (ν• E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′
   ⊖₁-✓ (ν•ᵇ_ {x = x} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ E/E′ | P′ with (swap *ᶜ) E/E′
   ... | swap*E/E′ rewrite swap-involutive (target E/E′) = P′
   ⊖₁-✓ (ν•ᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a | sym (swap∘suc-swap∘swap (target E/E′)) =
      ν (swap *⁼ ∘ suc swap *⁼) swap*P′
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u =
      ν ≈-trans ((swap *⁼ ∘ suc swap *⁼) swap*P′) (≈-reflexive (swap∘suc-swap∘swap (target E/E′)))
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | P′ = {!!} -- with (swap *ᶜ) E/E′ | (swap *ᶜ) E′/E
   -- ... | swap*E/E′ | swap*E′/E = ν (swap *⁼) P′
   -- ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) | E′/E ᵀΔ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   -- ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u | sym (swap∘suc-swap∘swap (target E/E′)) =
   --   ν (swap *⁼ ∘ suc swap *⁼) swap*P′
   ⊖₁-✓ (νᵛᵛ_ {x = x} {u} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | P′ = {!!}
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ _ | P′ with (swap *ᶜ) E′/E
   ... | swap*E′/E rewrite swap∘push∘push a′ = ν (swap *⁼) P′
   ⊖₁-✓ (νᶜᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = ν P′
   ⊖₁-✓ (! E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′

   -- Now symmetrise.
   ⊖-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (E⌣E′ : E ⌣[ a⌣a′ ] E′) → let open Delta′ (⊖ E⌣E′) in cofinal a⌣a′ S S′
   ⊖-✓ (inj₁ E⌣E′) = ⊖₁-✓ E⌣E′
   ⊖-✓ (inj₂ E′⌣E) with ⊖₁ E′⌣E | ⊖₁-✓ E′⌣E
   ⊖-✓ {a⌣a′ = ᵛ∇ᵛ} (inj₂ E′⌣E) | _ ᵀΔ _ | P′ = ≈-sym P′
   ⊖-✓ {a⌣a′ = ᵇ∇ᵇ} (inj₂ E′⌣E) | _ ᵀΔ _ | P′ = ≈-sym (≈-trans ((swap *⁼) P′) (≈-reflexive (swap-involutive _)))
   ⊖-✓ {a⌣a′ = ᵇ∇ᶜ} (inj₂ E′⌣E) | _ ᵀΔ _ | P′ = ≈-sym P′
   ⊖-✓ {a⌣a′ = ᶜ∇ᵇ} (inj₂ E′⌣E) | _ ᵀΔ _ | P′ = ≈-sym P′
   ⊖-✓ {a⌣a′ = ᶜ∇ᶜ} (inj₂ E′⌣E) | _ ᵀΔ _ | P′ = ≈-sym P′
