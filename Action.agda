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
   inc : ∀ {Γ} → Action Γ → Cxt
   inc (_ ᵇ) = ᴺ.suc zero
   inc (_ ᶜ) = zero

   -- The 5 kinds of coinitial action residual. The ᵛ∇ᵛ case is what really makes this necessary.
   data coinitial {Γ} : (a a′ : Action Γ) → Set where
      ᵛ∇ᵛ : {x u : Name Γ} → coinitial ((• x) ᵇ) ((• u) ᵇ)
      ᵇ∇ᵇ : {a a′ : Actionᵇ Γ} → coinitial (a ᵇ) (a′ ᵇ)
      ᵇ∇ᶜ : {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} → coinitial (a ᵇ) (a′ ᶜ)
      ᶜ∇ᵇ : {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} → coinitial (a ᶜ) (a′ ᵇ)
      ᶜ∇ᶜ : {a a′ : Actionᶜ Γ} → coinitial (a ᶜ) (a′ ᶜ)

   coinitial-sym : ∀ {Γ} {a a′ : Action Γ} → coinitial a a′ → coinitial a′ a
   coinitial-sym ᵛ∇ᵛ = ᵛ∇ᵛ
   coinitial-sym ᵇ∇ᵇ = ᵇ∇ᵇ
   coinitial-sym ᵇ∇ᶜ = ᶜ∇ᵇ
   coinitial-sym ᶜ∇ᵇ = ᵇ∇ᶜ
   coinitial-sym ᶜ∇ᶜ = ᶜ∇ᶜ
