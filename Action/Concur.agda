module Action.Concur where

   open import SharedModules

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ); open ᴬ.Action; open ᴬ.Actionᵇ
   open import Name using (Name)

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
