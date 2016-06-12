-- A renaming as a context morphism.
module Ren where

   open import ProofRelevantPiCommon hiding (Involutive)

   open import Data.Nat.Properties.Simple
   import Relation.Binary.EqReasoning as EqReasoning

   open import Name as ᴺ using (Cxt; module Cxt; Name; _+_; zero; shift)

   -- Hom-setoid over extensional equivalence. TODO: define a Category instance.
   Ren : Cxt → Cxt → Set
   Ren Γ Γ′ = Name Γ → Name Γ′

   -- Extend a renaming with an identity mapping. Should really be called - + 1.
   suc : ∀ {Γ Γ′} → Ren Γ Γ′ → Ren (Γ + 1) (Γ′ + 1)
   suc ρ zero = zero
   suc ρ (ᴺ.suc x) = ᴺ.suc (ρ x)

   push : ∀ {Γ} → Ren Γ (Γ + 1)
   push = shift 1

   weaken : ∀ {Γ} → Ren Γ (Γ + 1)
   weaken zero = zero
   weaken (ᴺ.suc x) = ᴺ.suc (weaken x)

   infixl 6 _ᴿ+_
   _ᴿ+_ : ∀ {Γ Γ′} → Ren Γ Γ′ → ∀ n → Ren (Γ + n) (Γ′ + n)
   ρ ᴿ+ zero = ρ
   ρ ᴿ+ (ᴺ.suc n) = suc (ρ ᴿ+ n)

   -- TODO: define a Functor instance for (ᴿ+ Δ).
   +-preserves-id : ∀ {Γ} Δ → (id {A = Name Γ} ᴿ+ Δ) ≃ₑ id
   +-preserves-id zero _ = refl
   +-preserves-id (ᴺ.suc _) zero = refl
   +-preserves-id (ᴺ.suc Δ) (ᴺ.suc x) = cong ᴺ.suc (+-preserves-id Δ x)

   +-preserves-≃ₑ : ∀ {Γ Γ′} Δ {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ ᴿ+ Δ ≃ₑ σ ᴿ+ Δ
   +-preserves-≃ₑ zero ρ≃ₑσ = ρ≃ₑσ
   +-preserves-≃ₑ (ᴺ.suc _) _ zero = refl
   +-preserves-≃ₑ (ᴺ.suc Δ) ρ≃ₑσ (ᴺ.suc x) = cong ᴺ.suc (+-preserves-≃ₑ Δ ρ≃ₑσ x)

   +-preserves-∘ : ∀ {Γ Δ Γ′} Δ′ (ρ : Ren Δ Γ′) (σ : Ren Γ Δ) → (ρ ᴿ+ Δ′) ∘ (σ ᴿ+ Δ′) ≃ₑ (ρ ∘ σ) ᴿ+ Δ′
   +-preserves-∘ zero _ _ _ = refl
   +-preserves-∘ (ᴺ.suc _) _ _ zero = refl
   +-preserves-∘ (ᴺ.suc Δ) ρ σ (ᴺ.suc x) = cong ᴺ.suc (+-preserves-∘ Δ ρ σ x)

   -- shift n is a natural transformation between the identity functor and (· ᴿ+ n).
   ᴿ+-comm : ∀ {Γ Γ′} n (ρ : Ren Γ Γ′) → (ρ ᴿ+ n) ∘ shift {Γ} n ≃ₑ shift {Γ′} n ∘ ρ
   ᴿ+-comm zero _ _ = refl
   ᴿ+-comm (ᴺ.suc n) ρ = cong ᴺ.suc ∘ ᴿ+-comm n ρ

   -- Functor from renamings.
   record Renameable (A : Cxt → Set) : Set where
      field
         _* : ∀ {Γ Γ′} → Ren Γ Γ′ → A Γ → A Γ′
         *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → ρ * ≃ₑ σ *
         *-preserves-id : ∀ {Γ} → id * ≃ₑ id {A = A Γ}
         *-preserves-∘ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → ρ * ∘ σ * ≃ₑ (ρ ∘ σ) *

      -- TODO: better names for these.
      ∘-*₁ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} {ρ′ : Ren Γ Γ′} →
             ρ ∘ σ ≃ₑ ρ′ → ρ * ∘ σ * ≃ₑ ρ′ *
      ∘-*₁ ρ∘σ≃ₑρ′ a = trans (*-preserves-∘ a) (*-preserves-≃ₑ ρ∘σ≃ₑρ′ a)

      ∘-* : ∀ {Γ Δ Δ′ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} {ρ′ : Ren Δ′ Γ′} {σ′ : Ren Γ Δ′} →
            ρ ∘ σ ≃ₑ ρ′ ∘ σ′ → ρ * ∘ σ * ≃ₑ ρ′ * ∘ σ′ *
      ∘-* ρ∘σ≡ρ′∘σ′ a = trans (∘-*₁ ρ∘σ≡ρ′∘σ′ a) (sym (*-preserves-∘ a))

   instance
      ᴺren : Renameable Name
      ᴺren = record {
            _* = λ ρ x → ρ x;
            *-preserves-≃ₑ = id;
            *-preserves-id = λ _ → refl;
            *-preserves-∘ = λ _ → refl
         }

   open Renameable ᴺren

   pop : ∀ {Γ} (x : Name Γ) → Ren (Γ + 1) Γ
   pop x zero = x
   pop _ (ᴺ.suc y) = y

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ρ ∘ pop {Γ} x ≃ₑ pop {Γ′} ((ρ *) x) ∘ suc ρ
   pop-comm _ x zero = refl
   pop-comm _ x (ᴺ.suc y) = refl

   swap : ∀ {Γ} → Ren (Γ + 2) (Γ + 2)
   swap zero = ᴺ.suc zero
   swap (ᴺ.suc zero) = zero
   swap (ᴺ.suc (ᴺ.suc x)) = ᴺ.suc (ᴺ.suc x)

   swap-suc-suc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → swap {Γ′} ∘ suc (suc ρ) ≃ₑ suc (suc ρ) ∘ swap {Γ}
   swap-suc-suc _ zero = refl
   swap-suc-suc _ (ᴺ.suc zero) = refl
   swap-suc-suc _ (ᴺ.suc (ᴺ.suc _)) = refl

   Involutive : ∀ {Γ} → Ren Γ Γ → Set
   Involutive ρ = ρ ∘ ρ ≃ₑ id

   +-preserves-involutivity : ∀ {Γ} (ρ : Ren Γ Γ) Δ → Involutive ρ → Involutive (ρ ᴿ+ Δ)
   +-preserves-involutivity ρ Δ ρ-involutive x =
      let open EqReasoning (setoid _) in
      begin
         (ρ ᴿ+ Δ) ((ρ ᴿ+ Δ) x)
      ≡⟨ +-preserves-∘ Δ ρ ρ _ ⟩
         ((ρ ∘ ρ) ᴿ+ Δ) x
      ≡⟨ +-preserves-≃ₑ Δ ρ-involutive _ ⟩
         (id ᴿ+ Δ) x
      ≡⟨ +-preserves-id Δ _ ⟩
         id x
      ∎

   swap-involutive : ∀ {Γ} → Involutive (swap {Γ})
   swap-involutive zero = refl
   swap-involutive (ᴺ.suc zero) = refl
   swap-involutive (ᴺ.suc (ᴺ.suc _)) = refl

   swap∘suc-swap∘swap : ∀ {Γ} → swap ∘ suc (swap {Γ}) ∘ swap ≃ₑ suc swap ∘ swap ∘ suc swap
   swap∘suc-swap∘swap zero = refl
   swap∘suc-swap∘swap (ᴺ.suc zero) = refl
   swap∘suc-swap∘swap (ᴺ.suc (ᴺ.suc zero)) = refl
   swap∘suc-swap∘swap (ᴺ.suc (ᴺ.suc (ᴺ.suc _))) = refl

   -- Additional properties required to prove cofinality of transition residuals.
   swap∘suc-push : ∀ {Γ} → push {Γ + 1} ≃ₑ swap ∘ suc push
   swap∘suc-push zero = refl
   swap∘suc-push (ᴺ.suc _) = refl

   swap∘push : ∀ {Γ} → suc (push {Γ}) ≃ₑ swap ∘ push {Γ + 1}
   swap∘push zero = refl
   swap∘push (ᴺ.suc _) = refl

   -- The names of the next two are too similar.
   pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) ≃ₑ pop ((push *) y) ∘ swap
   pop∘swap _ zero = refl
   pop∘swap _ (ᴺ.suc zero) = refl
   pop∘swap _ (ᴺ.suc (ᴺ.suc _)) = refl

   pop-swap : ∀ {Γ} → pop ᴺ.zero ∘ swap {Γ} ≃ₑ pop ᴺ.zero
   pop-swap zero = refl
   pop-swap (ᴺ.suc zero) = refl
   pop-swap (ᴺ.suc (ᴺ.suc _)) = refl

   pop∘suc-push : ∀ {Γ} (y : Name Γ) → push ∘ (pop y) ≃ₑ pop ((push *) y) ∘ suc push
   pop∘suc-push _ zero = refl
   pop∘suc-push _ (ᴺ.suc _) = refl

   pop-zero∘suc-push : ∀ {Γ} → pop {Γ + 1} ᴺ.zero ∘ suc push ≃ₑ id
   pop-zero∘suc-push zero = refl
   pop-zero∘suc-push (ᴺ.suc _) = refl

   pop-pop-swap : ∀ {Γ} (x y : Name Γ) → pop x ∘ suc (pop y) ∘ swap ≃ₑ pop y ∘ suc (pop x)
   pop-pop-swap _ _ zero = refl
   pop-pop-swap _ _ (ᴺ.suc zero) = refl
   pop-pop-swap _ _ (ᴺ.suc (ᴺ.suc _)) = refl

   suc-pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) ∘ swap ≃ₑ pop ((push *) y)
   suc-pop∘swap _ zero = refl
   suc-pop∘swap _ (ᴺ.suc zero) = refl
   suc-pop∘swap _ (ᴺ.suc (ᴺ.suc _)) = refl
