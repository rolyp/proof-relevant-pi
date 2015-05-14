open import Name as ᴺ using (Cxt)
open import Ren as ᴿ using (Renameable; Ren)

-- Agda can't infer the renaming arguments in many cases; these wrappers make them more explicit.
module Ren.Properties {A : Cxt → Set} ⦃ _ : Renameable A ⦄ where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext

   open ᴺ using (Name; _+_; zero; shift)
   open ᴿ using (module Renameable; suc; pop; push; _ᴿ+_; swap; ᴺren)

   module Renameable′ = Renameable {A = A}; open Renameable′ ⦃...⦄ -- fix A for all uses of *
   open Renameable ⦃...⦄ using () renaming (_* to _*′)

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

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ρ * ∘ pop x * ≃ₑ pop ((ρ *′) x) * ∘ suc ρ *
   pop-comm ρ x = ∘-* (ᴿ.pop-comm ρ x)

   ᴿ+-comm : ∀ {Γ Γ′} n (ρ : Ren Γ Γ′) → (ρ ᴿ+ n) * ∘ shift {Γ} n * ≃ₑ shift {Γ′} n * ∘ ρ *
   ᴿ+-comm n ρ = ∘-* (ᴿ.ᴿ+-comm n ρ)

   -- Additional properties required to prove cofinality of transition residuals.
   swap∘suc-push : ∀ {Γ} → push {Γ + 1} * ≃ₑ swap * ∘ suc push *
   swap∘suc-push a = sym (∘-*₁ (≃ₑ-sym ᴿ.swap∘suc-push) a)

   swap∘push : ∀ {Γ} → suc push * ≃ₑ swap * ∘ push {Γ + 2} *
   swap∘push a = sym (∘-*₁ (≃ₑ-sym ᴿ.swap∘push) a)

   pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) * ≃ₑ pop ((push *′) y) * ∘ swap {Γ} *
   pop∘swap y a = sym (∘-*₁ (≃ₑ-sym (ᴿ.pop∘swap y)) a)

   pop∘suc-push : ∀ {Γ} (y : Name Γ) → push * ∘ pop {Γ} y * ≃ₑ pop ((push *′) y) * ∘ suc push *
   pop∘suc-push y = ∘-* (ᴿ.pop∘suc-push y)
{-
   pop-zero∘suc-push : ∀ {Γ} (a : A (Γ + 1)) → pop zero * suc push * a ≡ a
   pop-zero∘suc-push a = trans (∘-*₁ a ᴿ.pop-zero∘suc-push) (*-preserves-id a)

   suc-pop∘swap : ∀ {Γ} (y : Name Γ) (a : A (Γ + 2)) → suc (pop y) * swap * a ≡ pop (push * y) * a
   suc-pop∘swap y a = ∘-*₁ a (ᴿ.suc-pop∘swap y)

   pop-pop-swap : ∀ {Γ} (x y : Name Γ) (a : A (Γ + 2)) → pop x * suc (pop y) * swap * a ≡ pop y * suc (pop x) * a
   pop-pop-swap x y a =
      begin
         pop x * suc (pop y) * swap * a
      ≡⟨ cong (_*_ (pop x)) (*-preserves-∘ a) ⟩
         pop x * (suc (pop y) ∘ swap) * a
      ≡⟨ ∘-* a (ᴿ.pop-pop-swap x y) ⟩
         pop y * suc (pop x) * a
      ∎ where open EqReasoning (setoid _)
-}
