module Transition.Concur.Properties where

   open import SharedModules

   open import Data.Fin using (Fin; toℕ)

   open import Action as ᴬ using (Action); open ᴬ.Actionᵇ
   import Action.Ren
   open import Name using (_+_; zero)
   open import Proc using (Proc)
   import Proc.Ren
   open import StructuralCong.Proc using (_≅_; module _≅_; ≅-refl; ≅-reflexive; ≅-sym; _*⁼);
      open _≅_ renaming (trans to ≅-trans)
   open import Ren as ᴿ using (Ren; ᴺren; suc; pop; push; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (_⌣₁_; module _⌣₁_; _⌣_; coinitial; module coinitial; _Δ_; _∶_Δ_; module _Δ_; ᴬ⊖; ᴬ⊖-✓; ⊖₁; ⊖);
      open _⌣₁_; open coinitial
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- structurally congruent, or structurally congruent with each other's swap image.
   cofinal : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : coinitial a a′) →
             let Γ′ = ᴬ.target (π₁ (ᴬ⊖ a⌣a′)) in Proc Γ′ → Proc Γ′ → Set
   cofinal ᵛ∇ᵛ = _≅_
   cofinal ᵇ∇ᵇ P₁ P₂ = P₁ ≅ (swap *) P₂
   cofinal ᵇ∇ᶜ = _≅_
   cofinal ᶜ∇ᵇ = _≅_
   cofinal ᶜ∇ᶜ = _≅_

   -- Correctness of residuals, with respect to the above notion of cofinality.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} (E⌣E′ : E ⌣₁ E′) →
           let open _Δ_ (⊖₁ E⌣E′) in cofinal a⌣a′ P₁ P₂
   ⊖₁-✓ (E ᵇ│ᵇ F) rewrite swap∘suc-push (target E) {-| ≃ₑ-sym (swap∘push (target F))-} = {!!} --≅-refl
   ⊖₁-✓ (E ᵇ│ᶜ F) = ≅-refl
   ⊖₁-✓ (E ᶜ│ᵇ F) = ≅-refl
   ⊖₁-✓ (E ᶜ│ᶜ F) = ≅-refl
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᵇ ∶ _ Δ E/E′ | swap*P′ with (pop y *ᵇ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a | pop∘swap y (target E/E′) = (pop ((push *) y) *⁼) swap*P′ │ ≅-refl
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᵇ ∶ _ Δ E/E′ | P′ with (pop y *ᶜ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a = (pop y *⁼) P′ │ ≅-refl
   ⊖₁-✓ (_ᵇ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᵇ∇ᶜ ∶ _ Δ _ | Q′ rewrite pop∘suc-push y (target E) = ≅-refl │ Q′
   ⊖₁-✓ (E ᶜ│• F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | Q′ = ≅-refl │ Q′
   ⊖₁-✓ (E⌣E′ │ᵥᵇ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | swap*P′ {-rewrite swap∘push (target F)-} = ν (swap*P′ │ {!!}) -- ≅-refl
   ⊖₁-✓ (E⌣E′ │ᵥᶜ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᵇ ∶ _ Δ _ | P′ = ν (P′ │ ≅-refl)
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᵛ∇ᵛ ∶ _ Δ _ | Q′ with (push *ᵇ) E
   ... | push*E rewrite pop-zero∘suc-push (target E) = ≅-refl │ Q′
   ⊖₁-✓ (E ᵇ│ᵥ F⌣F′) | ᵇ∇ᵇ ∶ _ Δ _ | swap*Q′ {-rewrite swap∘push (target E)-} = ν ({!!} │ swap*Q′) -- ≅-refl
   ⊖₁-✓ (E ᶜ│ᵥ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᶜ∇ᵇ ∶ _ Δ _ | Q′ = ν (≅-refl │ Q′)
   ⊖₁-✓ (P │ᵇᵇ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᵛ∇ᵛ ∶ _ Δ _ | Q′ = ≅-refl │ Q′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | swap*Q′ rewrite swap∘push∘push P = ≅-refl │ swap*Q′
   ⊖₁-✓ (P │ᵇᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᵇ∇ᶜ ∶ _ Δ _ | Q′ = ≅-refl │ Q′
   ⊖₁-✓ (P │ᶜᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | Q′ = ≅-refl │ Q′
   ⊖₁-✓ (E⌣E′ ᵇᵇ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵛ∇ᵛ ∶ _ Δ _ | P′ = P′ │ ≅-refl
   ... | ᵇ∇ᵇ ∶ _ Δ _ | swap*P′ rewrite swap∘push∘push Q = swap*P′ │ ≅-refl
   ⊖₁-✓ (E⌣E′ ᵇᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᶜ ∶ _ Δ _ | P′ = P′ │ ≅-refl
   ⊖₁-✓ (E⌣E′ ᶜᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = P′ │ ≅-refl
   ⊖₁-✓ (E⌣E′ ➕₁ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵛ∇ᵛ ∶ _ Δ _ | P′ = P′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | P′ = P′
   ... | ᵇ∇ᶜ ∶ _ Δ _ | P′ = P′
   ... | ᶜ∇ᵇ ∶ _ Δ _ | P′ = P′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = P′
   ⊖₁-✓ (_│•_ {x = x} {y} {u} {z} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᶜ∇ᶜ ∶ _ Δ _ | swap*P′ | Q′ with (pop y *ᵇ) E′/E | (pop z *ᵇ) E/E′
   ... | pop-y*E′/E | pop-z*E/E′ rewrite pop∘push u y | pop∘push x z | sym (pop-pop-swap z y (target E/E′)) =
      (pop z *⁼ ∘ suc (pop y) *⁼) swap*P′ │ Q′
   ⊖₁-✓ (_│•ᵥ_ {u = u} {y} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | ᵇ∇ᵇ ∶ E′/E Δ _ | ᶜ∇ᵇ ∶ _ Δ _ | swap*P′ | Q′ with (pop y *ᵇ) E′/E
   ... | pop-y*E′/E rewrite pop∘push u y =
      ν (≅-trans ((suc (pop y) *⁼) swap*P′) (≅-reflexive (suc-pop∘swap y _)) │ Q′)
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | ᵛ∇ᵛ ∶ _ Δ _ | swap*P′ | Q′ =
      ν (≅-trans ((pop zero *⁼) swap*P′) (≅-reflexive (pop-swap _)) │ Q′)
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᵇ∇ᵇ ∶ F′/F Δ F/F′ | swap*P′ | swap*Q′ =
      ≅-trans (ν (ν (swap*P′ │ swap*Q′))) (νν-swapₗ _)
   ⊖₁-✓ (ν• E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = P′
   ⊖₁-✓ (ν•ᵇ_ {x = x} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᵇ ∶ _ Δ E/E′ | P′ with (swap *ᶜ) E/E′
   ... | swap*E/E′ rewrite swap-involutive (target E/E′) = P′
   ⊖₁-✓ (ν•ᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = P′
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a | sym (swap∘suc-swap∘swap (target E/E′)) =
      ν (swap *⁼ ∘ suc swap *⁼) swap*P′
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u =
      ν ≅-trans ((swap *⁼ ∘ suc swap *⁼) swap*P′) (≅-reflexive (swap∘suc-swap∘swap (target E/E′)))
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵛ∇ᵛ ∶ E′/E Δ E/E′ | P′ with (swap *ᶜ) E/E′ | (swap *ᶜ) E′/E
   ... | swap*E/E′ | swap*E′/E {-rewrite ∘-*₁ x ᴿ.suc-push∘push | ∘-*₁ u ᴿ.suc-push∘push-} = ν (swap *⁼) P′
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u | sym (swap∘suc-swap∘swap (target E/E′)) =
      ν (swap *⁼ ∘ suc swap *⁼) swap*P′
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵇ∇ᶜ ∶ E′/E Δ _ | P′ with (swap *ᶜ) E′/E
   ... | swap*E′/E rewrite swap∘push∘push a′ = ν (swap *⁼) P′
   ⊖₁-✓ (νᶜᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = ν P′
   ⊖₁-✓ (! E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | ᵛ∇ᵛ ∶ _ Δ _ | P′ = P′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | P′ = P′
   ... | ᵇ∇ᶜ ∶ _ Δ _ | P′ = P′
   ... | ᶜ∇ᵇ ∶ _ Δ _ | P′ = P′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = P′

   -- Now symmetrise.
   ⊖-✓ : ∀ {Γ P} {a a′ : Action Γ} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} (E⌣E′ : E ⌣ E′) →
         let open _Δ_ (⊖ E⌣E′) in cofinal a⌣a′ P₁ P₂
   ⊖-✓ (inj₁ E⌣E′) = ⊖₁-✓ E⌣E′
   ⊖-✓ (inj₂ E′⌣E) with ⊖₁ E′⌣E | ⊖₁-✓ E′⌣E
   ... | ᵛ∇ᵛ ∶ _ Δ _ | P′ = ≅-sym P′
   ... | ᵇ∇ᵇ ∶ _ Δ _ | P′ = ≅-sym (≅-trans ((swap *⁼) P′) (≅-reflexive (swap-involutive _)))
   ... | ᵇ∇ᶜ ∶ _ Δ _ | P′ = ≅-sym P′
   ... | ᶜ∇ᵇ ∶ _ Δ _ | P′ = ≅-sym P′
   ... | ᶜ∇ᶜ ∶ _ Δ _ | P′ = ≅-sym P′
