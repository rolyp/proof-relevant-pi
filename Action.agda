-- Action transforming process in Γ.
module Action where

   open import SharedModules
   open import Name as ᴺ using (Cxt; Name; zero)

   data Actionᵇ (Γ : Cxt) : Set where
      _• : Name Γ → Actionᵇ Γ          -- bound input
      •_ : Name Γ → Actionᵇ Γ          -- bound output

   data Actionᶜ (Γ : Cxt) : Set where
      •_〈_〉 : Name Γ → Name Γ → Actionᶜ Γ   -- non-bound output
      τ : Actionᶜ Γ                           -- internal action

   data Action (Γ : Cxt) : Set where
      _ᵇ : Actionᵇ Γ → Action Γ
      _ᶜ : Actionᶜ Γ → Action Γ

   -- Shorthand for working with heterogeneous equality.
   Action↱ = subst Action
   Action↲ = ≡-subst-removable Action

   -- An action optionally bumps the context by a variable. We specify this "relatively" so that we can
   -- easily show that how an action operates on the context is preserved by a renaming.
   inc : ∀ {Γ} → Action Γ → Cxt
   inc (_ ᵇ) = ᴺ.suc zero
   inc (_ ᶜ) = zero
