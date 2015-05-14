-- A renaming as a context morphism, plus a pointed variant.
module Ren where

   open import SharedModules hiding (Involutive)
   import Relation.Binary.EqReasoning as EqReasoning

   open import Ext
   open import Name as ᴺ using (Cxt; module Cxt; Name; _+_; zero)

   -- A renaming ρ represented as a list whose nth element is ρ(n). (Defining a renaming as a function
   -- doesn't work so well, since ≡ is not extensional.)
   data Ren : Cxt → Cxt → Set where
      [] : ∀ {Γ} → Ren Cxt.zero Γ
      _∷_ : ∀ {Γ Γ′} → Name Γ′ → Ren Γ Γ′ → Ren (Γ + 1) Γ′

   infixr 5 _∷_

   module Local where
      -- Interpret a renaming as a function.
      infixr 8 _*_
      _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → Name Γ → Name Γ′
      (x ∷ _) * zero = x
      (_ ∷ ρ) * (ᴺ.suc y) = ρ * y

   _∘_ : ∀ {Γ₁ Γ₂ Γ₃} → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₂ → Ren Γ₁ Γ₃
   ρ ∘ [] = []
   ρ ∘ (x ∷ σ) = ρ Local.* x ∷ ρ ∘ σ

   infixr 9 _∘_

   -- Translate the range of a renaming by 1. Used by push.
   shift : ∀ {Γ Γ′} → Ren Γ Γ′ → Ren Γ (Γ′ + 1)
   shift [] = []
   shift (x ∷ ρ) = ᴺ.suc x ∷ shift ρ

   -- Extend a renaming with an identity mapping. Should really be called - + 1.
   suc : ∀ {Γ Γ′} → Ren Γ Γ′ → Ren (Γ + 1) (Γ′ + 1)
   suc ρ = zero ∷ shift ρ

   _ᴿ+_ : ∀ {Γ Γ′} → Ren Γ Γ′ → ∀ n → Ren (Γ + n) (Γ′ + n)
   ρ ᴿ+ zero = ρ
   ρ ᴿ+ (ᴺ.suc n) = suc (ρ ᴿ+ n)

   id : ∀ {Γ} → Ren Γ Γ
   id {Cxt.zero} = []
   id {Cxt.suc _} = suc id

   open import Agda.Primitive

   record Renameable {n : Level} (A : Cxt → Set n) : Set n where
      infixr 8 _*_
      field
         _*_ : ∀ {Γ Γ′} → Ren Γ Γ′ → A Γ → A Γ′
         ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (a : A Γ₁) → ρ * σ * a ≡ (ρ ∘ σ) * a
         id-* : ∀ {Γ} (a : A Γ) → id * a ≡ a

      ∘-*₁ : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} {ρ′ : Ren Γ₁ Γ₃}
             (a : A Γ₁) → ρ ∘ σ ≡ ρ′ → ρ * (σ * a) ≡ ρ′ * a
      ∘-*₁ {ρ = ρ} {σ} {ρ′} a ρ∘σ≡ρ′ =
         begin
            ρ * (σ * a)
         ≡⟨ ∘-*-factor a ⟩
            (ρ ∘ σ) * a
         ≡⟨ cong (flip _*_ a) ρ∘σ≡ρ′ ⟩
            ρ′ * a
         ∎ where open EqReasoning (setoid _)

      ∘-* : ∀ {Γ₁ Γ₂ Γ₂′ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} {ρ′ : Ren Γ₂′ Γ₃} {σ′ : Ren Γ₁ Γ₂′}
           (a : A Γ₁) → ρ ∘ σ ≡ ρ′ ∘ σ′ → ρ * σ * a ≡ ρ′ * σ′ * a
      ∘-* a ρ∘σ≡ρ′∘σ′ = trans (∘-*₁ a ρ∘σ≡ρ′∘σ′) (sym (∘-*-factor a))

   shift-* : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → shift ρ Local.* x ≡ ᴺ.suc (ρ Local.* x)
   shift-* [] ()
   shift-* (_ ∷ _) zero = refl
   shift-* (_ ∷ ρ) (ᴺ.suc x) = shift-* ρ x

   instance
      ᴺren : Renameable Name
      ᴺren = record { _*_ = Local._*_ ; ∘-*-factor = ∘-*-factor ; id-* = id-* }
         where
            ∘-*-factor : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} (x : Name Γ₁) →
                         ρ Local.* σ Local.* x ≡ (ρ ∘ σ) Local.* x
            ∘-*-factor {ρ = ρ} {_ ∷ _} zero = refl
            ∘-*-factor {ρ = ρ} {x ∷ σ} (ᴺ.suc y) = ∘-*-factor y

            id-* : ∀ {Γ} (x : Name Γ) → id Local.* x ≡ x
            id-* {Cxt.zero} ()
            id-* {Cxt.suc Γ} zero = refl
            id-* {Cxt.suc Γ} (ᴺ.suc x) rewrite shift-* id x | id-* x = refl

   open Renameable ᴺren

   ∘-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} (ρ₁ : Ren Γ₃ Γ₄) (ρ₂ : Ren Γ₂ Γ₃) (ρ₃ : Ren Γ₁ Γ₂) → ρ₁ ∘ (ρ₂ ∘ ρ₃) ≡ (ρ₁ ∘ ρ₂) ∘ ρ₃
   ∘-assoc ρ₁ ρ₂ [] = refl
   ∘-assoc ρ₁ ρ₂ (x ∷ ρ₃) = cong₂ _∷_ (∘-*-factor x) (∘-assoc ρ₁ ρ₂ ρ₃)

   ∷∘shift : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} {x : Name Γ₃} → ρ ∘ σ ≡ (x ∷ ρ) ∘ shift σ
   ∷∘shift {σ = []} = refl
   ∷∘shift {σ = y ∷ σ} = refl ⟨ cong₂ _∷_ ⟩ ∷∘shift

   id-rightId : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → ρ ∘ id ≡ ρ
   id-rightId {ρ = []} = refl
   id-rightId {ρ = x ∷ ρ} = cong (_∷_ x) (trans (sym ∷∘shift) id-rightId)

   id-leftId : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → id ∘ ρ ≡ ρ
   id-leftId {ρ = []} = refl
   id-leftId {ρ = x ∷ ρ} = id-* x ⟨ cong₂ _∷_ ⟩ id-leftId

   -- The successor function on natural numbers, qua renaming.
   push : ∀ {Γ} → Ren Γ (Γ + 1)
   push = shift id

   pop : ∀ {Γ} (x : Name Γ) → Ren (Γ + 1) Γ
   pop x = x ∷ id

   swap : ∀ {Γ} → Ren (Γ + 2) (Γ + 2)
   swap = ᴺ.suc zero ∷ zero ∷ shift push

   push-* : ∀ {Γ} (x : Name Γ) → push * x ≡ ᴺ.suc x
   push-* {Cxt.zero} ()
   push-* {Cxt.suc Γ} zero = refl
   push-* {Cxt.suc Γ} (ᴺ.suc x) rewrite shift-* push x | shift-* id x | id-* x = refl

   -- shift has some factorisation properties.
   push-shift : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → push ∘ ρ ≡ shift ρ
   push-shift {ρ = []} = refl
   push-shift {ρ = x ∷ ρ} = push-* x ⟨ cong₂ _∷_ ⟩ push-shift

   suc-shift : ∀ {Γ₁ Γ₂ Γ₃} {ρ : Ren Γ₂ Γ₃} {σ : Ren Γ₁ Γ₂} → suc ρ ∘ shift σ ≡ shift (ρ ∘ σ)
   suc-shift {σ = []} = refl
   suc-shift {ρ = ρ} {x ∷ σ} = shift-* ρ x ⟨ cong₂ _∷_ ⟩ suc-shift

   -- suc is a functor.
   suc-preserves-∘ : ∀ {Γ₁ Γ₂ Γ₃} (ρ : Ren Γ₂ Γ₃) (σ : Ren Γ₁ Γ₂) → suc ρ ∘ suc σ ≡ suc (ρ ∘ σ)
   suc-preserves-∘ ρ [] = refl
   suc-preserves-∘ ρ (x ∷ σ) = refl ⟨ cong₂ _∷_ ⟩ (shift-* ρ x ⟨ cong₂ _∷_ ⟩ suc-shift )

   push-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → suc ρ ∘ push {Γ} ≡ push {Γ′} ∘ ρ
   push-comm ρ =
      begin
         suc ρ ∘ push
      ≡⟨ suc-shift ⟩
         shift (ρ ∘ id)
      ≡⟨ cong shift id-rightId ⟩
         shift ρ
      ≡⟨ sym push-shift ⟩
         push ∘ ρ
      ∎ where open EqReasoning (setoid _)

   suc-push∘push : ∀ {Γ} → suc push ∘ push ≡ shift (push {Γ})
   suc-push∘push = trans (push-comm push) push-shift

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) → ρ ∘ pop {Γ} x ≡ pop {Γ′} (ρ * x) ∘ suc ρ
   pop-comm [] ()
   pop-comm (y ∷ ρ) x = refl ⟨ cong₂ _∷_ ⟩ (sym (id-* y) ⟨ cong₂ _∷_ ⟩ (
      begin
         (y ∷ ρ) ∘ shift id
      ≡⟨ sym ∷∘shift ⟩
         ρ ∘ id
      ≡⟨ trans id-rightId (sym id-leftId) ⟩
         id ∘ ρ
      ≡⟨ ∷∘shift ⟩
         pop ((y ∷ ρ) * x) ∘ shift ρ
      ∎)) where open EqReasoning (setoid _)

   pop∘push : ∀ {Γ} {x : Name Γ} → pop x ∘ push ≡ id
   pop∘push = trans (sym ∷∘shift) id-leftId

   -- shift (shift ρ) equalises renamings that differ only at zero and one, such as swap and id.
   swap∘shift-shift : ∀ {Γ Γ′} {ρ : Ren Γ Γ′} → swap ∘ shift (shift ρ) ≡ shift (shift ρ)
   swap∘shift-shift {Cxt.zero} {ρ = []} = refl
   swap∘shift-shift {Cxt.suc Γ} {ρ = x ∷ ρ} rewrite shift-* push x =
      cong ᴺ.suc (push-* x) ⟨ cong₂ _∷_ ⟩ swap∘shift-shift

   swap∘push∘push : ∀ {Γ} → swap ∘ push ∘ push ≡ push ∘ push {Γ}
   swap∘push∘push =
      begin
         swap ∘ push ∘ push
      ≡⟨ cong (_∘_ swap) push-shift  ⟩
         swap ∘ shift push
      ≡⟨ swap∘shift-shift ⟩
         shift push
      ≡⟨ sym push-shift ⟩
         push ∘ push
      ∎ where open EqReasoning (setoid _)

   swap-suc-suc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → swap {Γ′} ∘ suc (suc ρ) ≡ suc (suc ρ) ∘ swap {Γ}
   swap-suc-suc ρ = cong (λ σ → ᴺ.suc zero ∷ zero ∷ σ) (
      begin
         swap ∘ shift (shift ρ)
      ≡⟨ swap∘shift-shift ⟩
         shift (shift ρ)
      ≡⟨ cong (shift ∘ᶠ shift) (sym id-rightId) ⟩
         shift (shift (ρ ∘ id))
      ≡⟨ cong shift (sym suc-shift) ⟩
         shift (suc ρ ∘ push)
      ≡⟨ sym suc-shift ⟩
         suc (suc ρ) ∘ shift push
      ∎) where open EqReasoning (setoid _)

   Involutive : ∀ {Γ} → Ren Γ Γ → Set
   Involutive ρ = ρ ∘ ρ ≡ id

   swap-involutive : ∀ {Γ} → Involutive (swap {Γ})
   swap-involutive = cong (λ ρ → zero ∷ ᴺ.suc zero ∷ ρ) swap∘shift-shift

   swap∘suc-push : ∀ {Γ} → push {Γ + 1} ≡ swap ∘ suc push
   swap∘suc-push = cong (λ ρ → ᴺ.suc zero ∷ ρ) (sym swap∘shift-shift)

   swap∘push : ∀ {Γ} → suc (push {Γ}) ≡ swap ∘ push {Γ + 1}
   swap∘push =
      begin
         suc push
      ≡⟨ sym id-leftId ⟩
         id ∘ suc push
      ≡⟨ sym (cong (flip _∘_ (suc push)) swap-involutive) ⟩
         (swap ∘ swap) ∘ suc push
      ≡⟨ sym (∘-assoc swap swap (suc push)) ⟩
         swap ∘ swap ∘ suc push
      ≡⟨ sym (cong (_∘_ swap) swap∘suc-push) ⟩
         swap ∘ push
      ∎ where open EqReasoning (setoid _)

   pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) ≡ pop (push * y) ∘ swap
   pop∘swap y rewrite sym (sym (push-* y)) = cong (λ ρ → zero ∷ ᴺ.suc y ∷ ρ) (
      begin
         push
      ≡⟨ sym id-rightId ⟩
         push ∘ id
      ≡⟨ ∷∘shift ⟩
         (zero ∷ push) ∘ push
      ≡⟨ ∷∘shift ⟩
         (ᴺ.suc y ∷ zero ∷ push) ∘ shift push
      ∎) where open EqReasoning (setoid _)

   suc-pop∘swap : ∀ {Γ} (y : Name Γ) → suc (pop y) ∘ swap ≡ pop (push * y)
   suc-pop∘swap y =
      begin
         suc (pop y) ∘ swap
      ≡⟨ cong (flip _∘_ swap) (pop∘swap y) ⟩
         (pop (push * y) ∘ swap) ∘ swap
      ≡⟨ sym (∘-assoc (pop (push * y)) swap swap) ⟩
         pop (push * y) ∘ swap ∘ swap
      ≡⟨ cong (_∘_ _) swap-involutive ⟩
         pop (push * y) ∘ id
      ≡⟨ id-rightId ⟩
         pop (push * y)
      ∎ where open EqReasoning (setoid _)

   pop-swap : ∀ {Γ} → pop ᴺ.zero ∘ swap {Γ} ≡ pop ᴺ.zero
   pop-swap = cong (λ ρ → ᴺ.zero ∷ ᴺ.zero ∷ ρ) (
      begin
         pop zero ∘ shift push
      ≡⟨ sym ∷∘shift ⟩
         id ∘ push
      ≡⟨ id-leftId ⟩
         push
      ∎) where open EqReasoning (setoid _)

   pop∘suc-push : ∀ {Γ} (y : Name Γ) → push ∘ (pop y) ≡ pop (push * y) ∘ suc push
   pop∘suc-push y = cong (λ ρ → push * y ∷ ρ) (
      begin
         push ∘ id
      ≡⟨ trans id-rightId (sym id-leftId) ⟩
         id ∘ push
      ≡⟨ ∷∘shift ⟩
         pop (push * y) ∘ shift push
      ∎) where open EqReasoning (setoid _)

   pop-pop-swap : ∀ {Γ} (x y : Name Γ) → pop x ∘ suc (pop y) ∘ swap ≡ pop y ∘ suc (pop x)
   pop-pop-swap {Γ} x y = id-* y ⟨ cong₂ _∷_ ⟩ (sym (id-* x) ⟨ cong₂ _∷_ ⟩ (
      begin
         pop x ∘ suc (pop y) ∘ shift push
      ≡⟨ cong (_∘_ (pop x)) suc-shift ⟩
         pop x ∘ shift (pop y ∘ push)
      ≡⟨ cong (λ ρ → pop x ∘ shift ρ) pop∘push ⟩
         pop x ∘ push
      ≡⟨ trans pop∘push (sym pop∘push) ⟩
         pop y ∘ push
      ∎)) where open EqReasoning (setoid _)

   swap∘suc-swap∘swap : ∀ {Γ} → swap ∘ suc (swap {Γ}) ∘ swap ≡ suc swap ∘ swap ∘ suc swap
   swap∘suc-swap∘swap =
      cong (λ ρ → ᴺ.suc (ᴺ.suc ᴺ.zero) ∷ ᴺ.suc ᴺ.zero ∷ ᴺ.zero ∷ ρ) (
         begin
            swap ∘ suc swap ∘ shift (shift push)
         ≡⟨ cong (_∘_ swap) suc-shift ⟩
            swap ∘ shift (swap ∘ shift push)
         ≡⟨ cong (λ ρ → swap ∘ shift ρ) swap∘shift-shift ⟩
            swap ∘ shift (shift push)
         ≡⟨ swap∘shift-shift ⟩
            shift (shift push)
         ≡⟨ cong shift (sym swap∘shift-shift) ⟩
            shift (swap ∘ shift push)
         ≡⟨ sym suc-shift ⟩
            (suc swap ∘ shift (shift push))
         ≡⟨ cong (_∘_ (suc swap)) (sym swap∘shift-shift) ⟩
            (suc swap ∘ swap ∘ shift (shift push))
         ∎) where open EqReasoning (setoid _)

   pop-zero∘suc-push : ∀ {Γ} → pop ᴺ.zero ∘ suc push ≡ id {Γ + 1}
   pop-zero∘suc-push = cong (λ ρ → ᴺ.zero ∷ ρ) (trans (sym ∷∘shift) id-leftId)

   open Local public
