module Action.Seq where

   open import SharedModules
   open import Action using (Action; Actionᵇ; Actionᶜ; inc)
   open import Name as ᴺ using (Cxt; Name; _+_)

   -- Wanted a single _∷_ taking a (bound or non-bound) action, with (inc a) in its type. That caused mayhem.
   data Action⋆ (Γ : Cxt) : Set where
      []  : Action⋆ Γ
      _ᵇ∷_ : (a : Actionᵇ Γ) (a⋆ : Action⋆ (Γ + 1)) → Action⋆ Γ
      _ᶜ∷_ : (a : Actionᶜ Γ) (a⋆ : Action⋆ Γ) → Action⋆ Γ

   inc⋆ : ∀ {Γ} → Action⋆ Γ → Cxt
   inc⋆ [] = 0
   inc⋆ (a ᵇ∷ a⋆) = 1 + inc⋆ a⋆
   inc⋆ (a ᶜ∷ a⋆) = 0 + inc⋆ a⋆
