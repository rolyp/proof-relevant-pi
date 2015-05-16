module Action.Seq where

   open import SharedModules
   open import Action using (Action; inc{-; target-})
   open import Name as ᴺ using (Cxt; Name; _+_)

   data Action⋆ (Γ : Cxt) : Set where
      []  : Action⋆ Γ
      _∷_ : (a : Action Γ) (a⋆ : Action⋆ (Γ + inc a)) → Action⋆ Γ

   inc⋆ : ∀ {Γ} → Action⋆ Γ → Cxt
   inc⋆ [] = 0
   inc⋆ (a ∷ a⋆) = inc a + inc⋆ a⋆

-- target⋆ : ∀ {Γ} → Action⋆ Γ → Cxt
-- target⋆ {Γ} [] = Γ
-- target⋆ (_ ∷ a⋆) = target⋆ a⋆
