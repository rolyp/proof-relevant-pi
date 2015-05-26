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

   open ≈-Reasoning

   -- Correctness of residuals, with respect to the above notion of cofinality. Use ≈-Reasoning for maximum clarity.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → let open Delta′ (⊖₁ E⌣E′) in ⋈[ Γ , a , π₁ (ᴬ⊖ a⌣a′) , zero ] S S′
   ⊖₁-✓ (E ᵇ│ᵇ F) =
      let R = target E; S = target F in
      (begin
         (swap *) ((push *) R)
      ≡⟨ sym (swap∘push _) ⟩
         (suc push *) R
      ∎) │
      (begin
         (swap *) ((suc push *) S)
      ≡⟨ sym (swap∘suc-push _) ⟩
         (push *) S
      ∎)
   ⊖₁-✓ (E ᵇ│ᶜ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E ᶜ│ᵇ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E ᶜ│ᶜ F) = ≈-reflexive (*-preserves-id _) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | (swap *⁼) (⊖₁-✓ E⌣E′)
   ... | E′/E ᵀΔ E/E′ | swap*swap*S≈swap*S′ with (pop y *ᵇ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a =
      let S = target E′/E; S′ = target E/E′ in
      (begin
         (id *) ((pop ((push *) y) *) S)
      ≡⟨ *-preserves-id _ ⟩
         (pop ((push *) y) *) S
      ≡⟨ cong (pop ((push *) y) *) (sym (swap-involutive _)) ⟩
         (pop ((push *) y) *) ((swap *) ((swap *) S))
      ≈⟨ (pop ((push *) y) *⁼) swap*swap*S≈swap*S′ ⟩
         (pop ((push *) y) *) ((swap *) S′)
      ≡⟨ sym (pop∘swap y _) ⟩
         (suc (pop y) *) S′
      ∎) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ with (pop y *ᶜ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a =
      let S = target E′/E; S′ = target E/E′ in
      (begin
         (id *) ((pop y *) S)
      ≡⟨ *-preserves-id _ ⟩
         (pop y *) S
      ≡⟨ cong (pop y *) (sym (*-preserves-id _)) ⟩
         (pop y *) ((id *) S)
      ≈⟨ (pop y *⁼) id*S≈S′ ⟩
         (pop y *) S′
      ∎) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_ᵇ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | id*S₁≈S′₁ =
      let R = target E in
      (begin
         (id *) ((pop (ᴺ.suc y) *) ((suc push *) R))
      ≡⟨ *-preserves-id _ ⟩
         ((pop (ᴺ.suc y) *) ((suc push *) R))
      ≡⟨ sym (pop∘suc-push y _) ⟩
         (push *) ((pop y *) R)
      ∎) │ id*S₁≈S′₁
   ⊖₁-✓ (E ᶜ│• F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | id*S₁≈S′₁ = ≈-reflexive (*-preserves-id _) │ id*S₁≈S′₁
   ⊖₁-✓ (E⌣E′ │ᵥᵇ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*S≈S′ =
      let S = target E′/E; S′ = target E/E′; S₁ = target F in
      ν ((
         begin
            (suc id *) S
         ≡⟨ +-id-elim 1 _ ⟩
            S
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S)
         ≈⟨ (swap *⁼) swap*S≈S′ ⟩
            (swap *) S′
         ∎) │ (
         begin
            (suc id *) ((suc push *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            ((suc push *) S₁)
         ≡⟨ swap∘push _ ⟩
            (swap *) ((push *) S₁)
         ∎))
      where open ≈-Reasoning
   ⊖₁-✓ (E⌣E′ │ᵥᶜ F) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      ν ((
         begin
            (suc id *) S
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) S
         ≈⟨ id*S≈S′ ⟩
            S′
         ∎) │ ≈-reflexive (+-id-elim 1 _))
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | id*S₁≈S′₁ =
      let R = target E in
      (begin
         (id *) ((pop zero *) ((suc push *) R))
      ≡⟨ *-preserves-id _ ⟩
         ((pop zero *) ((suc push *) R))
      ≡⟨ pop-zero∘suc-push _ ⟩
         R
      ∎) │ id*S₁≈S′₁
   ⊖₁-✓ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | swap*S₁≈S′₁ rewrite swap∘push (target E) =
      let S₁ = target E′/E; S′₁ = target E/E′ in
      ν (≈-reflexive (+-id-elim 1 _) │
         (begin
            (suc id *) S₁
         ≡⟨ +-id-elim 1 _ ⟩
            S₁
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₁)
         ≈⟨ (swap *⁼) swap*S₁≈S′₁ ⟩
            (swap *) S′₁
         ∎))
   ⊖₁-✓ (E ᶜ│ᵥ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | id*S₁≈S′₁ =
      let S₁ = target E′/E; S′₁ = target E/E′ in
      ν (≈-reflexive (+-id-elim 1 _) │ (
         begin
            (suc id *) S₁
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) S₁
         ≈⟨ id*S₁≈S′₁ ⟩
            S′₁
         ∎))
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | id*S₁≈S′₁ =
      ≈-reflexive (*-preserves-id _) │ id*S₁≈S′₁
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | swap*S₁≈S′₁ rewrite swap∘push∘push P = ≈-refl │ swap*S₁≈S′₁
   ⊖₁-✓ (P │ᵇᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | id*S₁≈S′₁ = ≈-reflexive (*-preserves-id _) │ id*S₁≈S′₁
   ⊖₁-✓ (P │ᶜᶜ F⌣F′) with ⊖₁ F⌣F′ | ⊖₁-✓ F⌣F′
   ... | _ ᵀΔ _ | id*S₁≈S′₁ = ≈-reflexive (*-preserves-id _) │ id*S₁≈S′₁
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} E⌣E′ _) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | id*S≈S′ = id*S≈S′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} E⌣E′ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | swap*S≈S′ rewrite swap∘push∘push Q = swap*S≈S′ │ ≈-refl
   ⊖₁-✓ (E⌣E′ ᵇᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | id*S≈S′ = id*S≈S′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E⌣E′ ᶜᶜ│ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | id*S≈S′ = id*S≈S′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E⌣E′ ➕₁ Q) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | σ*S≈S′ = σ*S≈S′
   ⊖₁-✓ (_│•_ {x = x} {y} {u} {z} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | _ ᵀΔ _ | swap*S≈S′ | id*S₂≈S′₂ =
      let S = target E′/E; S′ = target E/E′ in
      (begin
         (id *) ((pop z *) ((suc (pop y) *) S))
      ≡⟨ *-preserves-id _ ⟩
         (pop z *) ((suc (pop y) *) S)
      ≡⟨ sym (pop-pop-swap y z _) ⟩
         (pop y *) ((suc (pop z) *) ((swap *) S))
      ≈⟨ (pop y *⁼) ((suc (pop z) *⁼) swap*S≈S′) ⟩
         (pop y *) ((suc (pop z) *) S′)
      ∎) │ id*S₂≈S′₂
   ⊖₁-✓ (_│•ᵥ_ {u = u} {y} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | F′/F ᵀΔ F/F′ | swap*S₁≈S′₁ | id*S₂≈S′₂ =
      let S₁ = target E′/E; S′₁ = target E/E′; S₂ = target F′/F; S′₂ = target F/F′ in
      ν ((
         begin
            (suc id *) ((suc (pop y) *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            (suc (pop y) *) S₁
         ≡⟨ cong (suc (pop y) *) (sym (swap-involutive _ )) ⟩
            (suc (pop y) *) ((swap *) ((swap *) S₁))
         ≈⟨ (suc (pop y) *⁼) ((swap *⁼) swap*S₁≈S′₁) ⟩
            (suc (pop y) *) ((swap *) S′₁)
         ≡⟨ suc-pop∘swap y _ ⟩
            (pop ((push *) y) *) S′₁
         ∎) │ (
         begin
            (suc id *) S₂
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) S₂
         ≈⟨ id*S₂≈S′₂ ⟩
            S′₂
         ∎))
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | F′/F ᵀΔ F/F′ | swap*S₁≈S′₁ | id*S₂≈S′₂ =
      let S₁ = target E′/E; S′₁ = target E/E′; S₂ = target F′/F; S′₂ = target F/F′ in
      ν ((
         begin
            (suc id *) ((pop zero *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            (pop zero *) S₁
         ≡⟨ sym (pop-swap _) ⟩
            (pop zero *) ((swap *) S₁)
         ≈⟨ (pop zero * *⁼) swap*S₁≈S′₁ ⟩
            (pop zero *) S′₁
         ∎) │ (
         begin
            (suc id *) S₂
         ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
            (id *) S₂
         ≈⟨ id*S₂≈S′₂ ⟩
            S′₂
         ∎))
   ⊖₁-✓ (_│ᵥ_ {x = x} {u} {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′ | ⊖₁-✓ E⌣E′ | ⊖₁-✓ F⌣F′
   ... | E′/E ᵀΔ E/E′ | F′/F ᵀΔ F/F′ | swap*S₁≈S′₁ | swap*S₂≈S′₂ =
      let S₁ = target E′/E; S′₁ = target E/E′; S₂ = target F′/F; S′₂ = target F/F′ in
      ≈-trans (ν (ν ((
         begin
            (suc (suc id) *) S₁
         ≡⟨ +-id-elim 2 _ ⟩
            S₁
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₁)
         ≈⟨ (swap *⁼) swap*S₁≈S′₁ ⟩
            (swap *) S′₁
         ∎) │ (
         begin
            (suc (suc id) *) S₂
         ≡⟨ +-id-elim 2 _ ⟩
            S₂
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₂)
         ≈⟨ (swap *⁼) swap*S₂≈S′₂ ⟩
            (swap *) S′₂
         ∎)))) (νν-swapₗ _)
   ⊖₁-✓ (ν• E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | id*S≈S′ = id*S≈S′
   ⊖₁-✓ (ν•ᵇ_ {x = x} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      begin
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) id*S≈S′ ⟩
         (swap *) S′
      ∎
   ⊖₁-✓ (ν•ᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | P′ = P′
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*S≈S′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) swap*S≈S′) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) swap*S≈S′) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | swap*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) swap*S≈S′) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵛᵛ_ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) id*S≈S′ ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ with (swap *ᶜ) E′/E
   ... | swap*E′/E rewrite swap∘push∘push a′ =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) id*S≈S′ ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᶜᶜ E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | E′/E ᵀΔ E/E′ | id*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      ν (begin
         (suc id *) S
      ≡⟨ *-preserves-≃ₑ suc-preserves-id _ ⟩
         (id *) S
      ≈⟨ id*S≈S′ ⟩
         S′
      ∎) --P′
   ⊖₁-✓ (! E⌣E′) with ⊖₁ E⌣E′ | ⊖₁-✓ E⌣E′
   ... | _ ᵀΔ _ | σ*S≈S′ = σ*S≈S′
{-

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
