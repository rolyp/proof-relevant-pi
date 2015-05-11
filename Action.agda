-- Action transforming process in Γ.
module Action where

   open import SharedModules
   open import Name as ᴺ using (Cxt; Name; zero; _+_; toℕ)

   data Actionᵇ (Γ : Cxt) : Set where
      _• : Name Γ → Actionᵇ Γ          -- bound input
      •_ : Name Γ → Actionᵇ Γ          -- bound output

   data Actionᶜ (Γ : Cxt) : Set where
      •_〈_〉 : Name Γ → Name Γ → Actionᶜ Γ   -- non-bound output
      τ : Actionᶜ Γ                           -- internal action

   data Action (Γ : Cxt) : Set where
      _ᵇ : Actionᵇ Γ → Action Γ
      _ᶜ : Actionᶜ Γ → Action Γ

   -- Action bumps the context by either 0 variables or 1 variable.
   inc : ∀ {Γ} → Action Γ → Name 2
   inc (_ ᵇ) = ᴺ.suc zero
   inc (_ ᶜ) = zero

   target : ∀ {Γ} → Action Γ → Cxt
   target {Γ} a = Γ + toℕ (inc a)
