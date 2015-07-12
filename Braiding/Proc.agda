module Braiding.Proc where

   open import SharedModules hiding ([_]; preorder) renaming (sym to ≡-sym; trans to ≡-trans)
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.PreorderReasoning

   open import Ext

   open import Name using (Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Ren
   open import Ren as ᴿ using (Ren; push; suc; swap; Renameable; module Renameable; ᴺren);
      open Renameable ⦃...⦄
   open import Ren.Properties

   -- Synactic equivalence "modulo" a single transposition of adjacent binders. In the de Bruijn setting
   -- this means equating ν (ν P) with ν (ν (swap * P)). Not a congruence, in contrast to the LFMTP 2015 setup.
   infix 4 _≈_
   infixl 6 _➕₁_ _➕₂_ _│₁_ _│₂_
   data _≈_ {Γ} : Proc Γ → Proc Γ → Set where
      -- Braiding case. Can derive the symmetric version, but found it hard to prove involutivity.
      νν-swapᵣ : ∀ P → ν (ν P) ≈ ν (ν (swap *) P)
      νν-swapₗ : ∀ P → ν (ν (swap *) P) ≈ ν (ν P)
      -- Propagate.
      Ο : Ο ≈ Ο
      _•∙_ : ∀ (x : Name Γ) {P P′} → P ≡ P′ → x •∙ P ≈ x •∙ P′
      •_〈_〉∙_ : ∀ (x y : Name Γ) {P P′} → P ≡ P′ → • x 〈 y 〉∙ P ≈ • x 〈 y 〉∙ P′
      _➕₁_ : ∀ {P Q R S} → P ≈ R → Q ≡ S → P ➕ Q ≈ R ➕ S
      _➕₂_ : ∀ {P Q R S} → P ≡ R → Q ≈ S → P ➕ Q ≈ R ➕ S
      _│₁_ : ∀ {P Q R S} → P ≈ R → Q ≡ S → P │ Q ≈ R │ S
      _│₂_ : ∀ {P Q R S} → P ≡ R → Q ≈ S → P │ Q ≈ R │ S
      ν_ : ∀ {P R} → P ≈ R → ν P ≈ ν R
      !_ : ∀ {P R} → P ≈ R → ! P ≈ ! R

   source : ∀ {Γ} {P P′ : Proc Γ} → P ≈ P′ → Proc Γ
   source {P = P} _ = P

   target : ∀ {Γ} {P P′ : Proc Γ} → P ≈ P′ → Proc Γ
   target {P′ = P′} _ = P′

   ≈-sym : ∀ {Γ} → Symmetric (_≈_ {Γ})
   ≈-sym (νν-swapᵣ P) = νν-swapₗ P
   ≈-sym (νν-swapₗ P) = νν-swapᵣ P
   ≈-sym Ο = Ο
   ≈-sym (x •∙ refl) = x •∙ refl
   ≈-sym (• x 〈 y 〉∙ refl) = • x 〈 y 〉∙ refl
   ≈-sym (P ➕₁ refl) = ≈-sym P ➕₁ refl
   ≈-sym (refl ➕₂ Q) = refl ➕₂ ≈-sym Q
   ≈-sym (P │₁ refl) = ≈-sym P │₁ refl
   ≈-sym (refl │₂ Q) = refl │₂ ≈-sym Q
   ≈-sym (ν P) = ν ≈-sym P
   ≈-sym (! P) = ! ≈-sym P

   ≈-sym-involutive : ∀ {Γ} {P P′ : Proc Γ} (φ : P ≈ P′) → ≈-sym (≈-sym φ) ≡ φ
   ≈-sym-involutive Ο = refl
   ≈-sym-involutive (x •∙ refl) = refl
   ≈-sym-involutive (• x 〈 y 〉∙ refl) = refl
   ≈-sym-involutive (φ ➕₁ refl) = cong (flip _➕₁_ refl) (≈-sym-involutive φ)
   ≈-sym-involutive (refl ➕₂ ψ) = cong (_➕₂_ refl) (≈-sym-involutive ψ)
   ≈-sym-involutive (φ │₁ refl) = cong (flip _│₁_ refl) (≈-sym-involutive φ)
   ≈-sym-involutive (refl │₂ ψ) = cong (_│₂_ refl) (≈-sym-involutive ψ)
   ≈-sym-involutive (νν-swapᵣ P) = refl
   ≈-sym-involutive (νν-swapₗ P) = refl
   ≈-sym-involutive (ν φ) = cong ν_ (≈-sym-involutive φ)
   ≈-sym-involutive (! φ) = cong !_ (≈-sym-involutive φ)

   -- Renaming commutes with ≈. This isn't a Renameable (i.e. functor from Ren), but rather
   -- the action of such a functor on a 2-cell.
   _*⁼ : ∀ {Γ Γ′ P R} (ρ : Ren Γ Γ′) → P ≈ R → (ρ *) P ≈ (ρ *) R
   (ρ *⁼) (νν-swapᵣ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapᵣ ((suc (suc ρ) *) P)
   (ρ *⁼) (νν-swapₗ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapₗ ((suc (suc ρ) *) P)
   -- Propagate.
   (ρ *⁼) Ο = Ο
   (ρ *⁼) (x •∙ P) = (ρ *) x •∙ cong (suc ρ *) P
   (ρ *⁼) (• x 〈 y 〉∙ P) = • (ρ *) x 〈 (ρ *) y 〉∙ cong (ρ *) P
   (ρ *⁼) (P ➕₁ Q) = (ρ *⁼) P ➕₁ cong (ρ *) Q
   (ρ *⁼) (P ➕₂ Q) = cong (ρ *) P ➕₂ (ρ *⁼) Q
   (ρ *⁼) (P │₁ Q) = (ρ *⁼) P │₁ cong (ρ *) Q
   (ρ *⁼) (P │₂ Q) = cong (ρ *) P │₂ (ρ *⁼) Q
   (ρ *⁼) (ν P) = ν (suc ρ *⁼) P
   (ρ *⁼) (! P) = ! (ρ *⁼) P
