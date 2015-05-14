-- A renaming as a context morphism.
module Ren where

   open import SharedModules hiding (Involutive)

   open import Data.Nat.Properties.Simple
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext
   open import Name as ᴺ using (Cxt; module Cxt; Name; _+_; zero; fromℕ; inject+; shift)

   -- Hom-setoid over extensional equivalence. TODO: define a Category instance.
   Ren : Cxt → Cxt → Set
   Ren Γ Γ′ = Name Γ → Name Γ′

   -- Extend a renaming with an identity mapping. Should really be called - + 1.
   suc : ∀ {Γ Γ′} → Ren Γ Γ′ → Ren (Γ + 1) (Γ′ + 1)
   suc ρ zero = zero
   suc ρ (ᴺ.suc x) = ᴺ.suc (ρ x)

   push : ∀ {Γ} → Ren Γ (Γ + 1)
   push = shift 1

   -- TODO: define a Functor instance for suc.
   suc-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → suc ρ ≃ₑ suc σ
   suc-preserves-≃ₑ ρ≃ₑσ zero = refl
   suc-preserves-≃ₑ ρ≃ₑσ (ᴺ.suc x) = cong ᴺ.suc (ρ≃ₑσ x)

   suc-preserves-∘ : ∀ {Γ Δ Γ′} (ρ : Ren Δ Γ′) (σ : Ren Γ Δ) → suc ρ ∘ suc σ ≃ₑ suc (ρ ∘ σ)
   suc-preserves-∘ _ _ zero = refl
   suc-preserves-∘ _ _ (ᴺ.suc _) = refl

   suc-preserves-id : ∀ {Γ} → suc (id {A = Name Γ}) ≃ₑ id
   suc-preserves-id zero = refl
   suc-preserves-id (ᴺ.suc x) = cong ᴺ.suc refl

   _ᴿ+_ : ∀ {Γ Γ′} → Ren Γ Γ′ → ∀ n → Ren (Γ + n) (Γ′ + n)
   ρ ᴿ+ zero = ρ
   ρ ᴿ+ (ᴺ.suc n) = suc (ρ ᴿ+ n)

   -- shift n is a natural transformation between the identity functor and (· ᴿ+ n).
   ᴿ+-comm : ∀ {Γ Γ′} n (ρ : Ren Γ Γ′) → ρ ᴿ+ n ∘ shift {Γ} n ≃ₑ shift {Γ′} n ∘ ρ
   ᴿ+-comm zero _ _ = refl
   ᴿ+-comm (ᴺ.suc n) ρ = cong ᴺ.suc ∘ ᴿ+-comm n ρ

   -- Functor-like thing. TODO: turn _*_ into a postfix operator.
   record Renameable (A : Cxt → Set) : Set where
      infixr 8 _*_
      field
         _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → A Γ → A Γ′
         *-preserves-≃ₑ : ∀ {Γ Γ′} {ρ σ : Ren Γ Γ′} → ρ ≃ₑ σ → _*_ ρ ≃ₑ _*_ σ
         id-* : ∀ {Γ} (a : A Γ) → id * a ≡ a
         ∘-*-factor : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} → _*_ ρ ∘ _*_ σ ≃ₑ _*_ (ρ ∘ σ)

      ∘-*₁ : ∀ {Γ Δ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} {ρ′ : Ren Γ Γ′} →
             ρ ∘ σ ≃ₑ ρ′ → ∀ a → ρ * σ * a ≡ ρ′ * a
      ∘-*₁ ρ∘σ≃ₑρ′ a = trans (∘-*-factor a) (*-preserves-≃ₑ ρ∘σ≃ₑρ′ a)

      ∘-* : ∀ {Γ Δ Δ′ Γ′} {ρ : Ren Δ Γ′} {σ : Ren Γ Δ} {ρ′ : Ren Δ′ Γ′} {σ′ : Ren Γ Δ′} →
            ρ ∘ σ ≃ₑ ρ′ ∘ σ′ → _*_ ρ ∘ _*_ σ ≃ₑ _*_ ρ′ ∘ _*_ σ′
      ∘-* ρ∘σ≡ρ′∘σ′ a = trans (∘-*₁ ρ∘σ≡ρ′∘σ′ a) (sym (∘-*-factor a))

   instance
      ᴺren : Renameable Name
      ᴺren = record { _*_ = λ ρ x → ρ x; *-preserves-≃ₑ = id; id-* = λ _ → refl; ∘-*-factor = λ _ → refl }

   open Renameable ᴺren

   pop : ∀ {Γ} (x : Name Γ) → Ren (Γ + 1) Γ
   pop x zero = x
   pop _ (ᴺ.suc n) = n

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ρ ∘ pop {Γ} x ≃ₑ pop {Γ′} (ρ * x) ∘ suc ρ
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

   swap-involutive : ∀ {Γ} → Involutive (swap {Γ})
   swap-involutive zero = refl
   swap-involutive (ᴺ.suc zero) = refl
   swap-involutive (ᴺ.suc (ᴺ.suc _)) = refl
