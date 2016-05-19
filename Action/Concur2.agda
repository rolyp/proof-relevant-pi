module Action.Concur2 where

   open import ProofRelevantPiCommon

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   import Action.Ren
   open import Name as ᴺ using (Cxt; Name; _+_; zero)
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄

   -- The 5 (modulo symmetry) kinds of concurrent action. The ˣ∇ˣ and ᵛ∇ᵛ cases are the interesting ones; the
   -- former represents concurrent extrusions of the _same_ binder, and the latter concurrent extrusion
   -- synchronisations of _different_ binders. TODO: make the component actions explicit, as per the paper?
   infix 4 _ᴬ⌣₁_
   data _ᴬ⌣₁_ {Γ} : Action Γ → Action Γ → Set where
      ˣ∇ˣ : {x u : Name Γ} → (• x) ᵇ ᴬ⌣₁ (• u) ᵇ
      ᵇ∇ᵇ : {a a′ : Actionᵇ Γ} → a ᵇ ᴬ⌣₁ a′ ᵇ
      ᵇ∇ᶜ : {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} → a ᵇ ᴬ⌣₁ a′ ᶜ
      ᶜ∇ᵇ : {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} → a ᶜ ᴬ⌣₁ a′ ᵇ
      ᶜ∇ᶜ : {a a′ : Actionᶜ Γ} → a ᶜ ᴬ⌣₁ a′ ᶜ
      ᵛ∇ᵛ : τ ᶜ ᴬ⌣₁ τ ᶜ

   _ᴬ⌣_ : ∀ {Γ} → Action Γ → Action Γ → Set
   a ᴬ⌣ a′ = a ᴬ⌣₁ a′ × a′ ᴬ⌣₁ a

   ᴬ⌣-sym : ∀ {Γ} → Symmetric (_ᴬ⌣_ {Γ})
   ᴬ⌣-sym = ×-swap

   -- Second component here abstracts over the two action constructors.
   ᴬΔ : ∀ {Γ} {a a′ : Action Γ} → a ᴬ⌣₁ a′ → Σ[ A ∈ Set ] (A → Action (Γ + inc a))
   ᴬΔ {Γ} ˣ∇ˣ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᵇ∇ᵇ = Actionᵇ (Γ + 1) , _ᵇ
   ᴬΔ {Γ} ᵇ∇ᶜ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᶜ∇ᵇ = Actionᵇ Γ , _ᵇ
   ᴬΔ {Γ} ᶜ∇ᶜ = Actionᶜ Γ , _ᶜ
   ᴬΔ {Γ} ᵛ∇ᵛ = Actionᶜ Γ , _ᶜ

   -- The residual a′/a. Note that ᵇ∇ᵇ may also relate two bound outputs, but only if they represent
   -- extrusions of distinct binders.
   ᴬ/ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣₁ a′) → π₁ (ᴬΔ a⌣a′)
   ᴬ/ (ˣ∇ˣ {u = u}) = • ᴺ.suc u 〈 zero 〉
   ᴬ/ (ᵇ∇ᵇ {a′ = a′}) = (push *) a′
   ᴬ/ (ᵇ∇ᶜ {a′ = a′}) = (push *) a′
   ᴬ/ (ᶜ∇ᵇ {a′ = a′}) = a′
   ᴬ/ (ᶜ∇ᶜ {a′ = a′}) = a′
   ᴬ/ ᵛ∇ᵛ = τ

   -- Symmetrise.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Action (Γ + inc a) × Action (Γ + inc a′)
   ᴬ⊖ (a⌣a′ , a′⌣a) = (π₂ (ᴬΔ a⌣a′) (ᴬ/ a⌣a′)) , (π₂ (ᴬΔ a′⌣a) (ᴬ/ a′⌣a))

   -- A pair of composable actions.
   Action₂ : Cxt → Set
   Action₂ Γ = Σ[ a ∈ Action Γ ] Action (Γ + inc a)
