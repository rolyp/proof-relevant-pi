-- Action transforming process in Γ.
module Action where

   open import SharedModules
   open import Name as ᴺ using (Cxt; Name; _+_)

   data Actionᵇ (Γ : Cxt) : Set where
      _• : Name Γ → Actionᵇ Γ          -- bound input
      •_ : Name Γ → Actionᵇ Γ          -- bound output

   data Actionᶜ (Γ : Cxt) : Set where
      •_〈_〉 : Name Γ → Name Γ → Actionᶜ Γ   -- non-bound output
      τ : Actionᶜ Γ                           -- internal action

   data Action (Γ : Cxt) : Set where
      _ᵇ : Actionᵇ Γ → Action Γ
      _ᶜ : Actionᶜ Γ → Action Γ

   target : ∀ {Γ} → Action Γ → Cxt
   target {Γ} (_ ᵇ) = Γ + 1
   target {Γ} (_ ᶜ) = Γ
