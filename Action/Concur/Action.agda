-- Residual of a′ ᴬ⌣ a″ after a. There are some cases that cannot arise; these should be harmless.
module Action.Concur.Action where

   open import SharedModules

   open import Action using (Action)
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_

   /-preserves-ᴬ⌣ : ∀ {Γ} {a a′ a″ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) (a′⌣a″ : a′ ᴬ⌣ a″) (a⌣a″ : a ᴬ⌣ a″) →
                    π₁ (ᴬ⊖ a⌣a′) ᴬ⌣ π₁ (ᴬ⊖ a⌣a″)
   /-preserves-ᴬ⌣ ˣ∇ˣ ˣ∇ˣ ˣ∇ˣ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ˣ∇ˣ ˣ∇ˣ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ˣ∇ˣ ᵇ∇ᵇ ˣ∇ˣ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ˣ∇ˣ ᵇ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ˣ∇ˣ ᵇ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ˣ∇ˣ ˣ∇ˣ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ˣ∇ˣ ᵇ∇ᵇ = ˣ∇ˣ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᵇ ˣ∇ˣ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᵇ ᵇ∇ᵇ = ᵇ∇ᵇ
   /-preserves-ᴬ⌣ ᵇ∇ᵇ ᵇ∇ᶜ ᵇ∇ᶜ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᵇ ˣ∇ˣ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᵇ ᵇ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᶜ∇ᶜ ᵇ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵇ∇ᶜ ᵛ∇ᵛ ᵇ∇ᶜ = ᵛ∇ᵛ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ˣ∇ˣ ᶜ∇ᵇ = ˣ∇ˣ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵇ∇ᵇ ᶜ∇ᵇ = ᵇ∇ᵇ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵇ∇ᶜ ᶜ∇ᶜ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᵇ ᵇ∇ᶜ ᵛ∇ᵛ = ᵇ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᶜ∇ᵇ ᶜ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᶜ∇ᶜ ᶜ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᶜ∇ᶜ ᵛ∇ᵛ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᵛ∇ᵛ ᶜ∇ᶜ = ᵛ∇ᵛ
   /-preserves-ᴬ⌣ ᶜ∇ᶜ ᵛ∇ᵛ ᵛ∇ᵛ = ᵛ∇ᵛ -- impossible
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᶜ∇ᵇ ᶜ∇ᵇ = ᶜ∇ᵇ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᶜ∇ᶜ ᶜ∇ᶜ = ᶜ∇ᶜ
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᶜ∇ᶜ ᵛ∇ᵛ = ᶜ∇ᶜ -- impossible
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵛ∇ᵛ ᶜ∇ᶜ = ᵛ∇ᵛ -- impossible
   /-preserves-ᴬ⌣ ᵛ∇ᵛ ᵛ∇ᵛ ᵛ∇ᵛ = ᵛ∇ᵛ
