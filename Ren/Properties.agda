open import Name as ᴺ using (Cxt)
open import Ren as ᴿ using (Renameable; Ren)

module Ren.Properties {A : Cxt → Set} ⦃ _ : Renameable A ⦄ where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open ᴺ using (Name; _+_; zero)
   open ᴿ using (module Renameable; _∷_; _∘_; ∘-assoc; shift; suc; id; pop; push; swap; ᴺren; id-rightId);
      open Renameable ⦃...⦄

   pop∘push : ∀ {Γ} (a : A Γ) (y : Name Γ) → pop y * push * a ≡ a
   pop∘push a y = trans (∘-*₁ a ᴿ.pop∘push) (id-* a)

   suc-push∘push : ∀ {Γ} (a : A Γ) → suc push * push * a ≡ shift push * a
   suc-push∘push a = ∘-*₁ a ᴿ.suc-push∘push

   push-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (a : A Γ) → suc ρ * push * a ≡ push * ρ * a
   push-comm ρ a = ∘-* a (ᴿ.push-comm ρ)

   involutive : ∀ {Γ} {ρ : Ren Γ Γ} → ᴿ.Involutive ρ → (a : A Γ) → ρ * ρ * a ≡ a
   involutive {ρ = ρ} ρ-involutive a = trans (∘-*₁ a ρ-involutive) (id-* a)

   swap-involutive : ∀ {Γ} (a : A (Γ + 2)) → swap * swap * a ≡ a
   swap-involutive = involutive ᴿ.swap-involutive

   swap∘push∘push : ∀ {Γ} (a : A Γ) → swap * push * push * a ≡ push * push * a
   swap∘push∘push a =
      begin
         swap * push * push * a
      ≡⟨ cong (_*_ swap) (∘-*-factor a) ⟩
         swap * (push ∘ push) * a
      ≡⟨ ∘-*₁ a ᴿ.swap∘push∘push ⟩
         (push ∘ push) * a
      ≡⟨ sym (∘-*-factor a) ⟩
         push * push * a
      ∎ where open EqReasoning (setoid _)

   swap-suc-suc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (a : A (Γ + 2)) → swap * suc (suc ρ) * a ≡ suc (suc ρ) * swap * a
   swap-suc-suc ρ a = ∘-* a (ᴿ.swap-suc-suc ρ)

   swap∘suc-push : ∀ {Γ} (a : A (Γ + 1)) → push * a ≡ swap * suc push * a
   swap∘suc-push a = sym (∘-*₁ a (sym ᴿ.swap∘suc-push))

   swap∘push : ∀ {Γ} (a : A (Γ + 1)) → suc push * a ≡ swap * push * a
   swap∘push a = sym (∘-*₁ a (sym ᴿ.swap∘push))

   pop-comm : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) (x : Name Γ) (a : A (Γ + 1)) → ρ * pop x * a ≡ pop (ρ * x) * suc ρ * a
   pop-comm ρ x a = ∘-* a (ᴿ.pop-comm ρ x)

   pop-swap : ∀ {Γ} (a : A (Γ + 2)) → pop zero * swap * a ≡ pop zero * a
   pop-swap a = ∘-*₁ a ᴿ.pop-swap

   pop-zero∘suc-push : ∀ {Γ} (a : A (Γ + 1)) → pop zero * suc push * a ≡ a
   pop-zero∘suc-push a = trans (∘-*₁ a ᴿ.pop-zero∘suc-push) (id-* a)

   swap∘suc-swap∘swap : ∀ {Γ} (a : A (Γ + 3)) → swap * suc swap * swap * a ≡ suc swap * swap * suc swap * a
   swap∘suc-swap∘swap a =
      begin
         swap * suc swap * swap * a
      ≡⟨ ∘-*-factor (swap * a) ⟩
         (swap ∘ suc swap) * swap * a
      ≡⟨ ∘-*₁ a (sym (∘-assoc _ _ swap))  ⟩
         (swap ∘ suc swap ∘ swap) * a
      ≡⟨ cong (flip _*_ a) ᴿ.swap∘suc-swap∘swap ⟩
         (suc swap ∘ swap ∘ suc swap) * a
      ≡⟨ cong (flip _*_ a) (∘-assoc _ _ (suc swap)) ⟩
         ((suc swap ∘ swap) ∘ suc swap) * a
      ≡⟨ trans (sym (∘-*-factor a)) (sym (∘-*-factor (suc swap * a))) ⟩
         suc swap * swap * suc swap * a
      ∎ where open EqReasoning (setoid _)

   pop∘swap : ∀ {Γ} (y : Name Γ) (a : A (Γ + 2)) → suc (pop y) * a ≡ pop (push * y) * swap * a
   pop∘swap y a = sym (∘-*₁ a (sym (ᴿ.pop∘swap y)))

   suc-pop∘swap : ∀ {Γ} (y : Name Γ) (a : A (Γ + 2)) → suc (pop y) * swap * a ≡ pop (push * y) * a
   suc-pop∘swap y a = ∘-*₁ a (ᴿ.suc-pop∘swap y)

   pop∘suc-push : ∀ {Γ} (y : Name Γ) (a : A (Γ + 1)) → push * pop y * a ≡ pop (push * y) * suc push * a
   pop∘suc-push y a = ∘-* a (ᴿ.pop∘suc-push y)

   pop-pop-swap : ∀ {Γ} (x y : Name Γ) (a : A (Γ + 2)) → pop x * suc (pop y) * swap * a ≡ pop y * suc (pop x) * a
   pop-pop-swap x y a =
      begin
         pop x * suc (pop y) * swap * a
      ≡⟨ cong (_*_ (pop x)) (∘-*-factor a) ⟩
         pop x * (suc (pop y) ∘ swap) * a
      ≡⟨ ∘-* a (ᴿ.pop-pop-swap x y) ⟩
         pop y * suc (pop x) * a
      ∎ where open EqReasoning (setoid _)
