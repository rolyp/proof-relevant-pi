module Transition.Concur.Cofinal where

   open import SharedModules

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; Action₂); open _ᴬ⌣_
   import Action.Ren
   open import Name as ᴺ using (Cxt; Name; toℕ; _+_; zero)
   open import Proc using (Proc); open Proc
   import Proc.Ren
   open import StructuralCong.Proc using (_≈_; module _≈_; ≈-refl; ≈-reflexive; ≈-sym; _*⁼; module ≈-Reasoning);
      open _≈_ renaming (trans to ≈-trans)
   open import Ren as ᴿ using (Ren; ᴺren; suc; _ᴿ+_; pop; push; swap; +-preserves-id); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; Delta; module Delta′; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- structurally congruent, or structurally congruent with each other's swap image.
   braid : ∀ {Γ} (ӓ : Action₂ Γ) → let Γ′ = Γ + inc (π₁ ӓ) + inc (π₂ ӓ) in Ren Γ′ Γ′
   braid (_ ᵇ , _ ᵇ) = swap
   braid (_ ᵇ , _ ᶜ) = id
   braid (_ ᶜ , _ ᵇ) = id
   braid (_ ᶜ , _ ᶜ) = id

   ⋈[_,_,_] : ∀ Γ (ӓ : Action₂ Γ) (Δ : Cxt) →
              let Γ′ = Γ + inc (π₁ ӓ) + inc (π₂ ӓ) in Proc (Γ′ + Δ) → Proc (Γ′ + Δ) → Set
   ⋈[ Γ , ӓ , Δ ] P P′ = ((braid ӓ ᴿ+ Δ) *) P ≈ P′

   open ≈-Reasoning
   open Delta′

   -- Correctness of residuals, with respect to the above notion of cofinality. Use ≈-Reasoning for maximum clarity.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (E⌣E′ : E ⌣₁[ a⌣a′ ] E′) → ⋈[ Γ , (a , π₁ (ᴬ⊖ a⌣a′)) , zero ] (S (⊖₁ E⌣E′)) (S′ (⊖₁ E⌣E′))
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
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with (pop y *ᵇ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      (begin
         (id *) ((pop ((push *) y) *) S)
      ≡⟨ *-preserves-id _ ⟩
         (pop ((push *) y) *) S
      ≡⟨ cong (pop ((push *) y) *) (sym (swap-involutive _)) ⟩
         (pop ((push *) y) *) ((swap *) ((swap *) S))
      ≈⟨ (pop ((push *) y) *⁼) ((swap *⁼) (⊖₁-✓ E⌣E′)) ⟩
         (pop ((push *) y) *) ((swap *) S′)
      ≡⟨ sym (pop∘swap y _) ⟩
         (suc (pop y) *) S′
      ∎) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with (pop y *ᶜ) (E/E′ (⊖₁ E⌣E′))
   ... | pop-y*E/E′ rewrite pop∘push y a =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      (begin
         (id *) ((pop y *) S)
      ≡⟨ *-preserves-id _ ⟩
         (pop y *) S
      ≡⟨ cong (pop y *) (sym (*-preserves-id _)) ⟩
         (pop y *) ((id *) S)
      ≈⟨ (pop y *⁼) (⊖₁-✓ E⌣E′) ⟩
         (pop y *) S′
      ∎) │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_ᵇ│•_ {y = y} E F⌣F′) =
      let R = target E in
      (begin
         (id *) ((pop (ᴺ.suc y) *) ((suc push *) R))
      ≡⟨ *-preserves-id _ ⟩
         ((pop (ᴺ.suc y) *) ((suc push *) R))
      ≡⟨ sym (pop∘suc-push y _) ⟩
         (push *) ((pop y *) R)
      ∎) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (E ᶜ│• F⌣F′) = ≈-reflexive (*-preserves-id _) │ (⊖₁-✓ F⌣F′)
   ⊖₁-✓ (E⌣E′ │ᵥᵇ F) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′); S₁ = target F in
      ν ((
         begin
            (suc id *) S
         ≡⟨ +-id-elim 1 _ ⟩
            S
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S)
         ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
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
   ⊖₁-✓ (E⌣E′ │ᵥᶜ F) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν ((
         begin
            (suc id *) S
         ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
            (id *) S
         ≈⟨ ⊖₁-✓ E⌣E′ ⟩
            S′
         ∎) │ ≈-reflexive (+-id-elim 1 _))
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {a⌣a′ = ᵛ∇ᵛ} E F⌣F′) =
      let R = target E in
      (begin
         (id *) ((pop zero *) ((suc push *) R))
      ≡⟨ *-preserves-id _ ⟩
         ((pop zero *) ((suc push *) R))
      ≡⟨ pop-zero∘suc-push _ ⟩
         R
      ∎) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E F⌣F′) rewrite swap∘push (target E) =
      let S₁ = S (⊖₁ F⌣F′); S′₁ = S′ (⊖₁ F⌣F′) in
      ν (≈-reflexive (+-id-elim 1 _) │
         (begin
            (suc id *) S₁
         ≡⟨ +-id-elim 1 _ ⟩
            S₁
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₁)
         ≈⟨ (swap *⁼) (⊖₁-✓ F⌣F′) ⟩
            (swap *) S′₁
         ∎))
   ⊖₁-✓ (E ᶜ│ᵥ F⌣F′) =
      let S₁ = S (⊖₁ F⌣F′); S′₁ = S′ (⊖₁ F⌣F′) in
      ν (≈-reflexive (+-id-elim 1 _) │ (
         begin
            (suc id *) S₁
         ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
            (id *) S₁
         ≈⟨ ⊖₁-✓ F⌣F′ ⟩
            S′₁
         ∎))
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P F⌣F′) = ≈-reflexive (*-preserves-id _) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P F⌣F′) rewrite swap∘push∘push P = ≈-refl │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (P │ᵇᶜ F⌣F′) = ≈-reflexive (*-preserves-id _) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (P │ᶜᵇ F⌣F′) = ≈-reflexive (*-preserves-id _) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (P │ᶜᶜ F⌣F′) = ≈-reflexive (*-preserves-id _) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} E⌣E′ _) = ⊖₁-✓ E⌣E′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} E⌣E′ Q) rewrite swap∘push∘push Q = ⊖₁-✓ E⌣E′ │ ≈-refl
   ⊖₁-✓ (E⌣E′ ᵇᶜ│ Q) = ⊖₁-✓ E⌣E′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E⌣E′ ᶜᵇ│ Q) = ⊖₁-✓ E⌣E′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E⌣E′ ᶜᶜ│ Q) = ⊖₁-✓ E⌣E′ │ ≈-reflexive (*-preserves-id _)
   ⊖₁-✓ (E⌣E′ ➕₁ Q) = ⊖₁-✓ E⌣E′
   ⊖₁-✓ (_│•_ {y = y} {z = z} E⌣E′ F⌣F′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      (begin
         (id *) ((pop z *) ((suc (pop y) *) S))
      ≡⟨ *-preserves-id _ ⟩
         (pop z *) ((suc (pop y) *) S)
      ≡⟨ sym (pop-pop-swap y z _) ⟩
         (pop y *) ((suc (pop z) *) ((swap *) S))
      ≈⟨ (pop y *⁼) ((suc (pop z) *⁼) (⊖₁-✓ E⌣E′)) ⟩
         (pop y *) ((suc (pop z) *) S′)
      ∎) │ ⊖₁-✓ F⌣F′
   ⊖₁-✓ (_│•ᵥ_ {y = y} E⌣E′ F⌣F′) =
      let S₁ = S (⊖₁ E⌣E′); S′₁ = S′ (⊖₁ E⌣E′); S₂ = S (⊖₁ F⌣F′); S′₂ = S′ (⊖₁ F⌣F′) in
      ν ((
         begin
            (suc id *) ((suc (pop y) *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            (suc (pop y) *) S₁
         ≡⟨ cong (suc (pop y) *) (sym (swap-involutive _ )) ⟩
            (suc (pop y) *) ((swap *) ((swap *) S₁))
         ≈⟨ (suc (pop y) *⁼) ((swap *⁼) (⊖₁-✓ E⌣E′)) ⟩
            (suc (pop y) *) ((swap *) S′₁)
         ≡⟨ suc-pop∘swap y _ ⟩
            (pop ((push *) y) *) S′₁
         ∎) │ (
         begin
            (suc id *) S₂
         ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
            (id *) S₂
         ≈⟨ ⊖₁-✓ F⌣F′ ⟩
            S′₂
         ∎))
   ⊖₁-✓ (_│ᵥ•_ {y = y} E⌣E′ F⌣F′) =
      let S₁ = S (⊖₁ E⌣E′); S′₁ = S′ (⊖₁ E⌣E′); S₂ = S (⊖₁ F⌣F′); S′₂ = S′ (⊖₁ F⌣F′) in
      ν ((
         begin
            (suc id *) ((pop (push y) *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            (pop (push y) *) S₁
         ≡⟨ sym (suc-pop∘swap y _) ⟩
            (suc (pop y) *) ((swap *) S₁)
         ≈⟨ (suc (pop y) *⁼) (⊖₁-✓ E⌣E′) ⟩
            (suc (pop y) *) S′₁
         ∎
      ) │ (
         begin
            (suc id *) S₂
         ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
            (id *) S₂
         ≈⟨ ⊖₁-✓ F⌣F′ ⟩
            S′₂
         ∎))
   ⊖₁-✓ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} E⌣E′ F⌣F′) =
      let S₁ = S (⊖₁ E⌣E′); S′₁ = S′ (⊖₁ E⌣E′); S₂ = S (⊖₁ F⌣F′); S′₂ = S′ (⊖₁ F⌣F′) in
      ν ((
         begin
            (suc id *) ((pop zero *) S₁)
         ≡⟨ +-id-elim 1 _ ⟩
            (pop zero *) S₁
         ≡⟨ sym (pop-swap _) ⟩
            (pop zero *) ((swap *) S₁)
         ≈⟨ (pop zero * *⁼) (⊖₁-✓ E⌣E′) ⟩
            (pop zero *) S′₁
         ∎) │ (
         begin
            (suc id *) S₂
         ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
            (id *) S₂
         ≈⟨ ⊖₁-✓ F⌣F′ ⟩
            S′₂
         ∎))
   ⊖₁-✓ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} E⌣E′ F⌣F′) =
      let S₁ = S (⊖₁ E⌣E′); S′₁ = S′ (⊖₁ E⌣E′); S₂ = S (⊖₁ F⌣F′); S′₂ = S′ (⊖₁ F⌣F′) in
      ≈-trans (ν (ν ((
         begin
            (suc (suc id) *) S₁
         ≡⟨ +-id-elim 2 _ ⟩
            S₁
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₁)
         ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
            (swap *) S′₁
         ∎) │ (
         begin
            (suc (suc id) *) S₂
         ≡⟨ +-id-elim 2 _ ⟩
            S₂
         ≡⟨ sym (swap-involutive _) ⟩
            (swap *) ((swap *) S₂)
         ≈⟨ (swap *⁼) (⊖₁-✓ F⌣F′) ⟩
            (swap *) S′₂
         ∎)))) (νν-swapₗ _)
   ⊖₁-✓ (ν• E⌣E′) = ⊖₁-✓ E⌣E′
   ⊖₁-✓ (ν•ᵇ E⌣E′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      begin
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
         (swap *) S′
      ∎
   ⊖₁-✓ (ν•ᶜ E⌣E′) = ⊖₁-✓ E⌣E′
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} E⌣E′) with (swap *ᵇ) (E/E′ (⊖₁ E⌣E′)) | (swap *ᵇ) (E′/E (⊖₁ E⌣E′))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ E⌣E′)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} E⌣E′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ E⌣E′)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} E⌣E′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ E⌣E′)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵛᵛ E⌣E′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} E⌣E′) with (swap *ᶜ) (E′/E (⊖₁ E⌣E′))
   ... | _ rewrite swap∘push∘push a′ =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᶜᵇ_ {a = a} E⌣E′) with (swap *ᶜ) (E/E′ (⊖₁ E⌣E′))
   ... | _ rewrite swap∘push∘push a =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ E⌣E′) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᶜᶜ E⌣E′) =
      let S = S (⊖₁ E⌣E′); S′ = S′ (⊖₁ E⌣E′) in
      ν (begin
         (suc id *) S
      ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
         (id *) S
      ≈⟨ ⊖₁-✓ E⌣E′ ⟩
         S′
      ∎)
   ⊖₁-✓ (! E⌣E′) = ⊖₁-✓ E⌣E′

   symmetrise : ∀ {Γ} {S S′ : Proc Γ} → (id *) S ≈ S′ → (id *) S′ ≈ S
   symmetrise {S = S} {S′} id*S≈S′ =
      begin
         (id *) S′
      ≡⟨ *-preserves-id _ ⟩
         S′
      ≈⟨ ≈-sym id*S≈S′ ⟩
         (id *) S
      ≡⟨ *-preserves-id _ ⟩
         S
      ∎

   -- Now symmetrise.
   ⊖-✓ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (E⌣E′ : E ⌣[ a⌣a′ ] E′) → ⋈[ Γ , (a , π₁ (ᴬ⊖ a⌣a′)) , zero ] (S (⊖ E⌣E′)) (S′ (⊖ E⌣E′))
   ⊖-✓ (inj₁ E⌣E′) = ⊖₁-✓ E⌣E′
   ⊖-✓ (inj₂ E′⌣E) with ⊖₁ E′⌣E | ⊖₁-✓ E′⌣E
   ⊖-✓ {a⌣a′ = ᵛ∇ᵛ} (inj₂ E′⌣E) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {a⌣a′ = ᵇ∇ᵇ} (inj₂ E′⌣E) | E′/E ᵀΔ E/E′ | swap*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      begin
         (swap *) S′
      ≈⟨ (swap *⁼) (≈-sym swap*S≈S′) ⟩
         (swap *) ((swap *) S)
      ≡⟨ swap-involutive _ ⟩
         S
      ∎
   ⊖-✓ {a⌣a′ = ᵇ∇ᶜ} (inj₂ E′⌣E) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {a⌣a′ = ᶜ∇ᵇ} (inj₂ E′⌣E) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {a⌣a′ = ᶜ∇ᶜ} (inj₂ E′⌣E) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
