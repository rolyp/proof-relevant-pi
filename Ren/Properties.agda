open import Name as ᴺ using (Cxt; +-assoc)
open import Ren as ᴿ using (Renameable; Ren)

-- Agda can't infer the renaming arguments in many cases; these wrappers make them more explicit.
module Ren.Properties {A : Cxt → Set} ⦃ _ : Renameable A ⦄ where

   open import ProofRelevantPiCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open ᴺ using (Name; _+_; zero; shift)
   open ᴿ using (module Renameable; suc; pop; push; _ᴿ+_; swap; +-preserves-id)

   module Renameable′ = Renameable {A = A}; open Renameable′ ⦃...⦄ -- fix A for all uses of *

   +-id-elim : ∀ {Γ} Δ → (id ᴿ+ Δ) * ≃ₑ id {A = A (Γ + Δ)}
   +-id-elim Δ a =
      begin
         ((id ᴿ+ Δ) *) a
      ≡⟨ *-preserves-≃ₑ (+-preserves-id Δ) _ ⟩
         (id *) a
      ≡⟨ *-preserves-id _ ⟩
         a
      ∎ where open EqReasoning (setoid _)

   involutive : ∀ {Γ} {ρ : Ren Γ Γ} → ᴿ.Involutive ρ → ρ * ∘ ρ * ≃ₑ id
   involutive {ρ = ρ} ρ-involutive a = trans (∘-*₁ ρ-involutive a) (*-preserves-id a)

   swap-involutive : ∀ {Γ} → swap {Γ} * ∘ swap * ≃ₑ id
   swap-involutive = involutive ᴿ.swap-involutive

   swap∘push∘push : ∀ {Γ} → swap {Γ} * ∘ push * ∘ push * ≃ₑ push * ∘ push *
   swap∘push∘push a = trans (cong (swap *) (*-preserves-∘ a)) (trans (∘-*₁ (λ _ → refl) a) (sym (*-preserves-∘ a)))

   swap-suc-suc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → swap * ∘ suc (suc ρ) * ≃ₑ suc (suc ρ) * ∘ swap {Γ} *
   swap-suc-suc ρ = ∘-* (ᴿ.swap-suc-suc ρ)

   swap∘suc-swap∘swap : ∀ {Γ} → swap {Γ + 1} * ∘ suc swap * ∘ swap * ≃ₑ suc swap * ∘ swap * ∘ suc swap *
   swap∘suc-swap∘swap a =
      begin
         (swap * ∘ suc swap * ∘ swap *) a
      ≡⟨ trans (*-preserves-∘ _) (*-preserves-∘ _) ⟩
         ((swap ∘ suc swap ∘ swap) *) a
      ≡⟨ *-preserves-≃ₑ (ᴿ.swap∘suc-swap∘swap) a ⟩
         ((suc swap ∘ swap ∘ suc swap) *) a
      ≡⟨ trans (sym (*-preserves-∘ _)) (sym (*-preserves-∘ _)) ⟩
         (suc swap * ∘ swap * ∘ suc swap *) a
      ∎ where open EqReasoning (setoid _)

   pop∘push : ∀ {Γ} (y : Name Γ) → pop y * ∘ push * ≃ₑ id
   pop∘push _ a = trans (*-preserves-∘ a) (*-preserves-id a)

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ρ * ∘ pop x * ≃ₑ pop (ρ x) * ∘ suc ρ *
   pop-comm ρ x = ∘-* (ᴿ.pop-comm ρ x)

   ᴿ+-comm : ∀ {Γ Γ′} n (ρ : Ren Γ Γ′) → (ρ ᴿ+ n) * ∘ shift {Γ} n * ≃ₑ shift {Γ′} n * ∘ ρ *
   ᴿ+-comm n ρ = ∘-* (ᴿ.ᴿ+-comm n ρ)

   -- Additional properties required to prove cofinality of transition residuals.
   swap∘suc-push : ∀ {Γ} → push {Γ + 1} * ≃ₑ swap * ∘ suc push *
   swap∘suc-push a = sym (∘-*₁ (≃ₑ-sym ᴿ.swap∘suc-push) a)

   swap∘push : ∀ {Γ} → suc push * ≃ₑ swap * ∘ push {Γ + 1} *
   swap∘push a = sym (∘-*₁ (≃ₑ-sym ᴿ.swap∘push) a)

   pop-swap : ∀ {Γ} → pop zero * ∘ swap {Γ} * ≃ₑ pop zero *
   pop-swap = ∘-*₁ ᴿ.pop-swap

   pop∘suc-push : ∀ {Γ} (y : Name Γ) → push * ∘ pop {Γ} y * ≃ₑ pop (ᴺ.suc y) * ∘ suc push *
   pop∘suc-push y = ∘-* (ᴿ.pop∘suc-push y)

   pop-zero∘suc-push : ∀ {Γ} → pop {Γ + 1} zero * ∘ suc push * ≃ₑ id
   pop-zero∘suc-push a = trans (∘-*₁ ᴿ.pop-zero∘suc-push a) (*-preserves-id a)

   pop-pop-swap : ∀ {Γ} (x y : Name Γ) → pop x * ∘ suc (pop y) * ∘ swap {Γ} * ≃ₑ pop y * ∘ suc (pop x) *
   pop-pop-swap x y a = trans (cong (pop x *) (*-preserves-∘ a)) (∘-* (ᴿ.pop-pop-swap x y) a)

   pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) * ≃ₑ pop (ᴺ.suc y) * ∘ swap {Γ} *
   pop∘swap y a = sym (∘-*₁ (≃ₑ-sym (ᴿ.pop∘swap y)) a)

   suc-pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) * ∘ swap {Γ} * ≃ₑ pop (ᴺ.suc y) *
   suc-pop∘swap y = ∘-*₁ (ᴿ.suc-pop∘swap y)

   swap-swap : ∀ {Γ} {a a′ : A (Γ + 2)} → (swap *) a ≡ a′ → a ≡ (swap *) a′
   swap-swap {a = a} {a′} swap*a≡a′ =
      let open EqReasoning (setoid _) in
      begin
         a
      ≡⟨ sym (swap-involutive _) ⟩
         (swap *) ((swap *) a)
      ≡⟨ cong (swap *) swap*a≡a′ ⟩
         (swap *) a′
      ∎

   id-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → id * ∘ ρ * ≃ₑ ρ * ∘ id *
   id-comm ρ a =
      begin
         (id *) ((ρ *) a)
      ≡⟨ *-preserves-id _ ⟩
         (ρ *) a
      ≡⟨ sym (cong (ρ *) (*-preserves-id _)) ⟩
         (ρ *) ((id *) a)
      ∎ where open EqReasoning (setoid _)
