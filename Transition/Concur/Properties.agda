module Transition.Concur.Properties where

   open import SharedModules

   open import Data.Fin using (Fin; toℕ)

   open import Action as ᴬ using (Action; inc; _ᴬ⌣_; module _ᴬ⌣_; ᴺinc-inc);
      open ᴬ.Action; open ᴬ.Actionᵇ; open _ᴬ⌣_
   import Action.Ren
   open import Name as ᴺ using (Cxt; Name; fromℕ≤; _+_; zero)
   open import Proc using (Proc); open Proc
   import Proc.Ren
   open import StructuralCong.Proc using (_≈_; module _≈_; ≈-refl; ≈-reflexive; ≈-sym; _*⁼; module ≈-Reasoning);
      open _≈_ renaming (trans to ≈-trans)
   open import Ren as ᴿ using (Ren; ᴺren; suc; _ᴿ+_; pop; push; swap; suc-preserves-id); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; Delta; module Delta′; ᴬ⊖; ᴬ⊖-✓; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- structurally congruent, or structurally congruent with each other's swap image.
   braid : ∀ {Γ} (a : Action Γ) (a′ : Action (Γ + inc a)) → let Γ′ = Γ + inc a + inc a′ in Ren Γ′ Γ′
   braid (_ ᵇ) (_ ᵇ) = swap
   braid (_ ᵇ) (_ ᶜ) = id
   braid (_ ᶜ) (_ ᵇ) = id
   braid (_ ᶜ) (_ ᶜ) = id

   ⋈[_,_,_,_] : ∀ Γ (a : Action Γ) (a′ : Action (Γ + inc a)) (m : Cxt) →
                let Γ′ = Γ + inc a + inc a′ in Proc (Γ′ + m) → Proc (Γ′ + m) → Set
   ⋈[ Γ , a , a′ , m ] P P′ = ((braid a a′ ᴿ+ m) *) P ≈ P′

   -- Correctness of residuals, with respect to the above notion of cofinality.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → let open Delta′ (⊖₁ E⌣E′) in ⋈[ Γ , a , π₁ (ᴬ⊖ a⌣a′) , zero ] S S′
   ⊖₁-✓ (E ᵇ│ᵇ F) = ≈-reflexive (sym (swap∘push _)) │ ≈-reflexive (sym (swap∘suc-push _))
   ⊖₁-✓ (E ᵇ│ᶜ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E ᶜ│ᵇ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E ᶜ│ᶜ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | (swap *⁼) (⊖₁-✓ E⌣E′)
   ... | E′/E ᵀΔ E/E′ | swap*S with (pop y *ᵇ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a | pop∘swap y (target E/E′) | swap-involutive (target E′/E) |
      *-preserves-id ((pop ((push *) y) *) (target E′/E)) =
      ≈-sym ((pop ((push *) y) *⁼) (≈-sym swap*S)) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | S with (pop y *ᶜ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a | *-preserves-id (target E′/E) | *-preserves-id ((pop y *) (target E′/E)) =
      (pop y *⁼) S │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_ᵇ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ rewrite pop∘suc-push y (target E) = ≈-reflexive (*-preserves-id _) │ Q′
   ⊖₁-✓ (E ᶜ│• F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-reflexive (*-preserves-id _) │ Q′
   ⊖₁-✓ (E⌣E′ │ᵥᵇ F) with ⊖₁ E⌣E′ | (swap *⁼) (⊖₁-✓ E⌣E′)
   ... | E′/E ᵀΔ E/E′ | swap*S′ =
      let S = target E′/E; S′ = target E/E′; S₁ = target F in
      ν ((
         begin
            (suc id *) S
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) S
         ≡⟨ *-preserves-id _ ⟩
            S
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S)
         ≈⟨ swap*S′ ⟩
            (swap *) S′
         ∎) │ (
         begin
            (suc id *) ((suc push *) S₁)
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) ((suc push *) S₁)
         ≡⟨ *-preserves-id _ ⟩
            ((suc push *) S₁)
         ≈⟨ {!!} ⟩
            (swap *) ((push *) S₁)
         ∎))
-- rewrite swap∘push (target F) | *-preserves-≃ₑ suc-preserves-id (target E′/E) |
--      swap-involutive (target E′/E) | *-preserves-id (target E′/E) |
--      *-preserves-≃ₑ suc-preserves-id ((swap *) ((push *) (target F))) | *-preserves-id ((swap *) ((push *) (target F))) =
--      ν (swap*S′ │ ≈-refl)
      where open ≈-Reasoning
   ⊖₁-✓ E⌣E′ = {!!}
{-
   ⊖₁-✓ (E⌣E′ │ᵥᶜ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = ν (P′ │ ≈-refl)
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ with (push *ᵇ) E
   ... | push*E rewrite pop-zero∘suc-push (target E) = ≈-refl │ Q′
   ⊖₁-✓ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | swap*Q′ rewrite swap∘push (target E) = ν (≈-refl │ swap*Q′)
   ⊖₁-✓ (E ᶜ│ᵥ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ν (≈-refl │ Q′)
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | swap*Q′ rewrite swap∘push∘push P = ≈-refl │ swap*Q′
   ⊖₁-✓ (P │ᵇᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (P │ᶜᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | Q′ = ≈-refl │ Q′
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} E⌣E′ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′ │ ≈-refl
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} E⌣E′ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | swap*P′ rewrite swap∘push∘push Q = swap*P′ │ ≈-refl
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
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | _ ᵀΔ _ | swap*P′ | Q′ = ν (≈-trans ((pop zero *⁼) swap*P′) (≈-reflexive (pop-swap _)) │ Q′)
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | _ ᵀΔ _ | swap*P′ | swap*Q′ = ≈-trans (ν (ν (swap*P′ │ swap*Q′))) (νν-swapₗ _)
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
   ... | E′/E ᵀΔ E/E′ | swap*P′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u | sym (swap∘suc-swap∘swap (target E/E′)) =
      ν (swap *⁼ ∘ suc swap *⁼) swap*P′
   ⊖₁-✓ (νᵛᵛ_ {x = x} {u} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | P′ = ν (swap *⁼) P′
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
-}
