module Action.Concur where

   open import ProofRelevantPiCommon

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   import Action.Ren
   open import Name as ᴺ using (Cxt; Name; _+_; zero)
   open import Ren as ᴿ using (push); open ᴿ.Renameable ⦃...⦄

   -- The 5 (modulo symmetry) kinds of concurrent action. The ˣ∇ˣ and ᵛ∇ᵛ cases are the interesting ones; the
   -- former represents concurrent extrusions of the _same_ binder, and the latter concurrent extrusion
   -- synchronisations of _different_ binders. TODO: make the component actions explicit, as per the paper?
   infix 4 _ᴬ⌣_
   data _ᴬ⌣_ {Γ} : (a a′ : Action Γ) → Set where
      ˣ∇ˣ : {x u : Name Γ} → (• x) ᵇ ᴬ⌣ (• u) ᵇ
      ᵇ∇ᵇ : {a a′ : Actionᵇ Γ} → a ᵇ ᴬ⌣ a′ ᵇ
      ᵇ∇ᶜ : {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} → a ᵇ ᴬ⌣ a′ ᶜ
      ᶜ∇ᵇ : {a : Actionᶜ Γ} {a′ : Actionᵇ Γ} → a ᶜ ᴬ⌣ a′ ᵇ
      ᶜ∇ᶜ : {a a′ : Actionᶜ Γ} → a ᶜ ᴬ⌣ a′ ᶜ
      ᵛ∇ᵛ : τ ᶜ ᴬ⌣ τ ᶜ

   ᴬ⌣-sym : ∀ {Γ} → Symmetric (_ᴬ⌣_ {Γ})
   ᴬ⌣-sym ˣ∇ˣ = ˣ∇ˣ
   ᴬ⌣-sym ᵇ∇ᵇ = ᵇ∇ᵇ
   ᴬ⌣-sym ᵇ∇ᶜ = ᶜ∇ᵇ
   ᴬ⌣-sym ᶜ∇ᵇ = ᵇ∇ᶜ
   ᴬ⌣-sym ᶜ∇ᶜ = ᶜ∇ᶜ
   ᴬ⌣-sym ᵛ∇ᵛ = ᵛ∇ᵛ

   ᴬ⌣-sym-involutive : ∀ {Γ} {a a′ : Action Γ} → (a⌣a′ : a ᴬ⌣ a′) → ᴬ⌣-sym (ᴬ⌣-sym a⌣a′) ≡ a⌣a′
   ᴬ⌣-sym-involutive ˣ∇ˣ = refl
   ᴬ⌣-sym-involutive ᵇ∇ᵇ = refl
   ᴬ⌣-sym-involutive ᵇ∇ᶜ = refl
   ᴬ⌣-sym-involutive ᶜ∇ᵇ = refl
   ᴬ⌣-sym-involutive ᶜ∇ᶜ = refl
   ᴬ⌣-sym-involutive ᵛ∇ᵛ = refl

   -- Second component here abstracts over the two action constructors.
   ᴬΔ : ∀ {Γ} {a a′ : Action Γ} → a ᴬ⌣ a′ → Σ[ A ∈ Set ] (A → Action (Γ + inc a))
   ᴬΔ {Γ} ˣ∇ˣ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᵇ∇ᵇ = Actionᵇ (Γ + 1) , _ᵇ
   ᴬΔ {Γ} ᵇ∇ᶜ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᶜ∇ᵇ = Actionᵇ Γ , _ᵇ
   ᴬΔ {Γ} ᶜ∇ᶜ = Actionᶜ Γ , _ᶜ
   ᴬΔ {Γ} ᵛ∇ᵛ = Actionᶜ Γ , _ᶜ

   -- The residual a′/a. Note that ᵇ∇ᵇ may also relate two bound outputs, but only if they represent
   -- extrusions of distinct binders.
   ᴬ/ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → π₁ (ᴬΔ a⌣a′)
   ᴬ/ (ˣ∇ˣ {u = u}) = • ᴺ.suc u 〈 zero 〉
   ᴬ/ (ᵇ∇ᵇ {a′ = a′}) = (push *) a′
   ᴬ/ (ᵇ∇ᶜ {a′ = a′}) = (push *) a′
   ᴬ/ (ᶜ∇ᵇ {a′ = a′}) = a′
   ᴬ/ (ᶜ∇ᶜ {a′ = a′}) = a′
   ᴬ/ ᵛ∇ᵛ = τ

   -- Symmetrise.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Action (Γ + inc a) × Action (Γ + inc a′)
   ᴬ⊖ a⌣a′ = π₂ (ᴬΔ a⌣a′) (ᴬ/ a⌣a′) , π₂ (ᴬΔ (ᴬ⌣-sym a⌣a′)) (ᴬ/ (ᴬ⌣-sym a⌣a′))

   -- A pair of composable actions.
   Action₂ : Cxt → Set
   Action₂ Γ = Σ[ a ∈ Action Γ ] Action (Γ + inc a)

   -- Cofinality of action residuals is simply agreement on target context.
   ᴬ⊖-✓ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Γ + inc a + inc (π₁ (ᴬ⊖ a⌣a′)) ≡ Γ + inc a′ + inc (π₂ (ᴬ⊖ a⌣a′))
   ᴬ⊖-✓ ˣ∇ˣ = refl
   ᴬ⊖-✓ ᵇ∇ᵇ = refl
   ᴬ⊖-✓ ᵇ∇ᶜ = refl
   ᴬ⊖-✓ ᶜ∇ᵇ = refl
   ᴬ⊖-✓ ᶜ∇ᶜ = refl
   ᴬ⊖-✓ ᵛ∇ᵛ = refl
