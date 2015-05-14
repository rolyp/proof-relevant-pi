-- In progress: generalise cofinality to traces.
module Transition.Concur.Properties2 where

   open import SharedModules

   open import Action as ᴬ using ()
   open import Name as ᴺ using (Cxt; Name; _+_; zero; suc; toℕ)
   open import Proc using (Proc)
   open import StructuralCong.Proc using (_≅_; module _≅_); open _≅_
   open import Ren as ᴿ using (Ren; id; suc; _ᴿ+_; swap); open ᴿ.Renameable ⦃...⦄
   open import Transition as ᵀ using (_—[_-_]→_; _—[_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (_⌣₁_; module _⌣₁_; module coinitial; _∶_Δ_; module _Δ_; ᴬ⊖; ᴬ⊖-✓; ⊖₁);
      open _⌣₁_; open coinitial

   braid : ∀ {Γ} (n : Name 3) → Ren (Γ + toℕ n) (Γ + toℕ n)
   braid zero = id
   braid (suc zero) = id
   braid (suc (suc zero)) = swap
   braid (suc (suc (suc ())))

   ⋈[_,_,_] : ∀ Γ (n : Name 3) (m : Cxt) → Proc ((Γ + toℕ n) + m) → Proc ((Γ + toℕ n) + m) → Set
   ⋈[_,_,_] Γ n m P₁ P₂ = (braid n) ᴿ+ m * P₁ ≅ P₂

   -- Observe that concurrent transitions from Γ have targets in Γ + n for some n ∈ {0, 1, 2}.
   -- TODO: think about baking this into the definition of residual.
   convert : ∀ {Γ} {P : Proc Γ} {a a′ R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} (E⌣E′ : E ⌣₁ E′) →
             let open _Δ_ (⊖₁ E⌣E′ ) in
             Σ[ n ∈ Name 3 ] (ᴬ.target (π₁ (ᴬ⊖ a⌣a′)) ≡ Γ + toℕ n) × Proc (Γ + toℕ n) × Proc (Γ + toℕ n)
   convert E⌣E′ with ⊖₁ E⌣E′
   convert E⌣E′ | ᵛ∇ᵛ ∶ E′/E Δ E/E′ = ᴺ.suc zero , refl , target E′/E , target E/E′
   convert E⌣E′ | ᵇ∇ᵇ ∶ E′/E Δ E/E′ = ᴺ.suc (ᴺ.suc zero) , refl , target E′/E , target E/E′
   convert E⌣E′ | ᵇ∇ᶜ ∶ E′/E Δ E/E′ = ᴺ.suc zero , refl , target E′/E , target E/E′
   convert E⌣E′ | ᶜ∇ᵇ ∶ E′/E Δ E/E′ = ᴺ.suc zero , refl , target E′/E , target E/E′
   convert E⌣E′ | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = zero , refl , target E′/E , target E/E′

   -- Correctness of residuals, with respect to the above notion of cofinality. TODO: symmetrise.
   postulate
     ⊖₁-✓ : ∀ {Γ} {P : Proc Γ} {a a′ R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} (E⌣E′ : E ⌣₁ E′) →
            let (n , _ , P₁ , P₂) = convert E⌣E′ in ⋈[ Γ , n , zero ] P₁ P₂
