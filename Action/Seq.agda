module Action.Seq where

   open import SharedModules
   open import Action using (Action; target)
   open import Name as ᴺ using (Cxt; Name; _+_)

   data Action⋆ (Γ : Cxt) : Set where
      []  : Action⋆ Γ
      _∷_ : (a : Action Γ) (a⋆ : Action⋆ (target a)) → Action⋆ Γ

   target⋆ : ∀ {Γ} → Action⋆ Γ → Cxt
   target⋆ {Γ} [] = Γ
   target⋆ (_ ∷ a⋆) = target⋆ a⋆
