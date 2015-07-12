module Braiding.Transition where

   open import SharedModules

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Braiding.Proc as ᴾ⁼ using (_⋈_; _*⁼; ⋈-sym; _⋉_; ⋉-refl); open ᴾ⁼._⋈_; open ᴾ⁼._⋉_
   open import Action.Ren
   open import Proc.Ren
   open import Ren as ᴿ using (suc; push; pop; swap; ᴺren; module Renameable); open Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren

   -- The type of the symmetric residual (φ/E , E/φ) for a single transition.
   infixl 5 _Δ⁼_
   record _Δ⁼_ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ⋈ P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         φ/E : R ⋉ R′
         E/φ : P′ —[ a - ι ]→ R′

   -- The symmetric residual. TODO: make infix.
   ⊖ : ∀ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ⋈ P′) → E Δ⁼ φ
   ⊖ (ν• (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = ν {!!} {-(sym (swap-involutive _))-} Δ (νᵇ (ν• swap*E))
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = {!!} {-refl-} Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (target E)))
   ... | swap*E | νν rewrite swap-involutive P | swap∘suc-swap∘swap (target E) =
      νν Δ {!!} -- νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (target E)))
   ... | swap*E | νν rewrite swap-involutive P | swap∘suc-swap∘swap (target E) =
      νν Δ {!!} --νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P | swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   ⊖ (ν•_ {x = x} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ν {!!} {-(sym (swap-involutive _))-} Δ νᵇ (ν• swap*E)
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ⋉-refl Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (target E)))
   ... | swap*E | νν rewrite swap∘suc-swap∘swap (target E) = νν Δ {!!} -- νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (target E)))
   ... | swap*E | νν rewrite swap∘suc-swap∘swap (target E) = νν Δ {!!} --νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   ⊖ (E ➕₁ Q) (φ ➕₁ refl) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ (E/φ ➕₁ Q)
   ⊖ (E ➕₁ Q) (refl ➕₂ ψ) = ⋉-refl Δ (E ➕₁ ᴾ⁼.target ψ)
   ⊖ (E ᵇ│ Q) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-(φ/E │₁ refl)-} Δ (E/φ ᵇ│ Q)
   ⊖ (E ᶜ│ Q) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-(φ/E │₁ refl)-} Δ (E/φ ᶜ│ Q)
   ⊖ (P │ᵇ F) (φ │₁ refl) = ({!!} │₁ refl) {-((push *⁼) φ -} Δ (ᴾ⁼.target φ │ᵇ F)
   ⊖ (P │ᶜ F) (φ │₁ refl) = {!!} {-(φ │₁ refl)-} Δ (ᴾ⁼.target φ │ᶜ F)
   ⊖ (E ᵇ│ Q) (refl │₂ ψ) = {!!} {-(refl │₂ (push *⁼) ψ)-} Δ (E ᵇ│ ᴾ⁼.target ψ)
   ⊖ (E ᶜ│ Q) (refl │₂ ψ) = {!!} {-(refl │₂ ψ)-} Δ (E ᶜ│ ᴾ⁼.target ψ)
   ⊖ (P │ᵇ F) (refl │₂ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in {!!} {-(refl │₂ ψ/F)-} Δ (P │ᵇ F/ψ)
   ⊖ (P │ᶜ F) (refl │₂ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in {!!} {-(refl │₂ ψ/F)-} Δ (P │ᶜ F/ψ)
   ⊖ (_│•_ {y = y} E F) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-((pop y *⁼) φ/E │₁ refl)-} Δ (E/φ │• F)
   ⊖ (E │• F) (refl │₂ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in {!!} {-(refl │₂ ψ/F)-} Δ (E │• F/ψ)
   ⊖ (E │ᵥ F) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-(ν (φ/E │₁ refl))-} Δ (E/φ │ᵥ F)
   ⊖ (E │ᵥ F) (refl │₂ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in {!!} {- (ν (refl │₂ ψ/F))-} Δ (E │ᵥ F/ψ)
   ⊖ (ν• E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ ν• E/φ
   ⊖ (νᵇ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-ν ((swap *⁼) φ/E)-} Δ νᵇ E/φ
   ⊖ (νᶜ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in {!!} {-ν φ/E-} Δ νᶜ E/φ
   ⊖ (! E) (! φ) = let φ/E Δ E/φ = ⊖ E (φ │₁ refl) in φ/E Δ {!!} -- ! E/φ
