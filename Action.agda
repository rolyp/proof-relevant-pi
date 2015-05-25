-- Action transforming process in Γ.
module Action where

   open import SharedModules
   open import Name as ᴺ using (Cxt; Name; zero; _+_; toℕ; fromℕ≤; _<_; module _≤_); open _≤_

   data Actionᵇ (Γ : Cxt) : Set where
      _• : Name Γ → Actionᵇ Γ          -- bound input
      •_ : Name Γ → Actionᵇ Γ          -- bound output

   data Actionᶜ (Γ : Cxt) : Set where
      •_〈_〉 : Name Γ → Name Γ → Actionᶜ Γ   -- non-bound output
      τ : Actionᶜ Γ                           -- internal action

   data Action (Γ : Cxt) : Set where
      _ᵇ : Actionᵇ Γ → Action Γ
      _ᶜ : Actionᶜ Γ → Action Γ

   -- An action optionally bumps the context by a variable.
   inc : ∀ {Γ} → Action Γ → Cxt
   inc (_ ᵇ) = ᴺ.suc zero
   inc (_ ᶜ) = zero

   -- Composed actions bump the context by at most two variables.
   inc-inc : ∀ {Γ} (a : Action Γ) (a′ : Action (Γ + inc a)) → inc a + inc a′ < 3
   inc-inc (_ ᵇ) (_ ᵇ) = s≤s (s≤s (s≤s z≤n))
   inc-inc (_ ᵇ) (_ ᶜ) = s≤s (s≤s z≤n)
   inc-inc (_ ᶜ) (_ ᵇ) = s≤s (s≤s z≤n)
   inc-inc (_ ᶜ) (_ ᶜ) = s≤s z≤n

   -- Not sure if it would be more convenient to have inc return a Name 2.
   ᴺinc-inc : ∀ {Γ} (a : Action Γ) (a′ : Action (Γ + inc a)) → Name 3
   ᴺinc-inc a a′ = fromℕ≤ (inc-inc a a′)

   -- The 5 kinds of concurrent action. The ᵛ∇ᵛ case is what really makes this necessary.
   infix 4 _ᴬ⌣_
   data _ᴬ⌣_ {Γ} : (a a′ : Action Γ) → Set where
      ᵛ∇ᵛ : {x u : Name Γ} → (• x) ᵇ ᴬ⌣ (• u) ᵇ
      ᵇ∇ᵇ : {a a′ : Actionᵇ Γ} → a ᵇ ᴬ⌣ a′ ᵇ
      ᵇ∇ᶜ : {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} → a ᵇ ᴬ⌣ a′ ᶜ
      ᶜ∇ᵇ : {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} → a ᶜ ᴬ⌣ a′ ᵇ
      ᶜ∇ᶜ : {a a′ : Actionᶜ Γ} → a ᶜ ᴬ⌣ a′ ᶜ

   ᴬ⌣-sym : ∀ {Γ} → Symmetric (_ᴬ⌣_ {Γ})
   ᴬ⌣-sym ᵛ∇ᵛ = ᵛ∇ᵛ
   ᴬ⌣-sym ᵇ∇ᵇ = ᵇ∇ᵇ
   ᴬ⌣-sym ᵇ∇ᶜ = ᶜ∇ᵇ
   ᴬ⌣-sym ᶜ∇ᵇ = ᵇ∇ᶜ
   ᴬ⌣-sym ᶜ∇ᶜ = ᶜ∇ᶜ

   ᴬ⌣-sym-involutive : ∀ {Γ} {a a′ : Action Γ} → (a⌣a′ : a ᴬ⌣ a′) → ᴬ⌣-sym (ᴬ⌣-sym a⌣a′) ≡ a⌣a′
   ᴬ⌣-sym-involutive ᵛ∇ᵛ = refl
   ᴬ⌣-sym-involutive ᵇ∇ᵇ = refl
   ᴬ⌣-sym-involutive ᵇ∇ᶜ = refl
   ᴬ⌣-sym-involutive ᶜ∇ᵇ = refl
   ᴬ⌣-sym-involutive ᶜ∇ᶜ = refl
