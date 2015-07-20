-- Symmetric, irreflexive relation that relates processes that differ by exactly one transposition of
-- adjacent binders, without proceeding under prefixes. In the de Bruijn setting, this means relating ν (ν P)
-- to ν (ν (swap * P)), and then closing under constructors other than 0, input and output. Was a congruence
-- in the LFMTP 2015 paper.
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

   infix 4 _⋈_
   infixl 6 _➕₁_ _➕₂_ _│₁_ _│₂_
   data _⋈_ {Γ} : Proc Γ → Proc Γ → Set where
      -- Braiding cases. Can derive the symmetric version but found it hard to prove involutivity.
      νν-swapᵣ : ∀ P → ν (ν P) ⋈ ν (ν (swap *) P)
      νν-swapₗ : ∀ P → ν (ν (swap *) P) ⋈ ν (ν P)
      -- Propagate.
      _➕₁_ : ∀ {P Q R S} → P ⋈ R → Q ≡ S → P ➕ Q ⋈ R ➕ S
      _➕₂_ : ∀ {P Q R S} → P ≡ R → Q ⋈ S → P ➕ Q ⋈ R ➕ S
      _│₁_ : ∀ {P Q R S} → P ⋈ R → Q ≡ S → P │ Q ⋈ R │ S
      _│₂_ : ∀ {P Q R S} → P ≡ R → Q ⋈ S → P │ Q ⋈ R │ S
      ν_ : ∀ {P R} → P ⋈ R → ν P ⋈ ν R
      !_ : ∀ {P R} → P ⋈ R → ! P ⋈ ! R

   ⋈-sym : ∀ {Γ} → Symmetric (_⋈_ {Γ})
   ⋈-sym (νν-swapᵣ P) = νν-swapₗ P
   ⋈-sym (νν-swapₗ P) = νν-swapᵣ P
   ⋈-sym (P ➕₁ refl) = ⋈-sym P ➕₁ refl
   ⋈-sym (refl ➕₂ Q) = refl ➕₂ ⋈-sym Q
   ⋈-sym (P │₁ refl) = ⋈-sym P │₁ refl
   ⋈-sym (refl │₂ Q) = refl │₂ ⋈-sym Q
   ⋈-sym (ν P) = ν ⋈-sym P
   ⋈-sym (! P) = ! ⋈-sym P

   ⋈-sym-involutive : ∀ {Γ} {P P′ : Proc Γ} (φ : P ⋈ P′) → ⋈-sym (⋈-sym φ) ≡ φ
   ⋈-sym-involutive (φ ➕₁ refl) = cong (flip _➕₁_ refl) (⋈-sym-involutive φ)
   ⋈-sym-involutive (refl ➕₂ ψ) = cong (_➕₂_ refl) (⋈-sym-involutive ψ)
   ⋈-sym-involutive (φ │₁ refl) = cong (flip _│₁_ refl) (⋈-sym-involutive φ)
   ⋈-sym-involutive (refl │₂ ψ) = cong (_│₂_ refl) (⋈-sym-involutive ψ)
   ⋈-sym-involutive (νν-swapᵣ P) = refl
   ⋈-sym-involutive (νν-swapₗ P) = refl
   ⋈-sym-involutive (ν φ) = cong ν_ (⋈-sym-involutive φ)
   ⋈-sym-involutive (! φ) = cong !_ (⋈-sym-involutive φ)

   -- Reflexive closure of ⋈, representing at most (rather than exactly) one braid.
   -- Defined explicitly so we have (a suitably "affine" notion of) compatibility by definition.
   infix 4 _⋉_
   data _⋉_ {Γ} : Proc Γ → Proc Γ → Set where
      -- Braiding cases.
      νν-swapᵣ : ∀ P → ν (ν P) ⋉ ν (ν (swap *) P)
      νν-swapₗ : ∀ P → ν (ν (swap *) P) ⋉ ν (ν P)
      -- Propagate.
      _➕₁_ : ∀ {P Q R S} → P ⋉ R → Q ≡ S → P ➕ Q ⋉ R ➕ S
      _➕₂_ : ∀ {P Q R S} → P ≡ R → Q ⋉ S → P ➕ Q ⋉ R ➕ S
      _│_ : ∀ {P Q R S} → P ⋉ R → Q ⋉ S → P │ Q ⋉ R │ S
      ν_ : ∀ {P R} → P ⋉ R → ν P ⋉ ν R
      !_ : ∀ {P R} → P ⋉ R → ! P ⋉ ! R
      -- Close under additional process constructors for reflexivity.
      Ο : Ο ⋉ Ο
      _•∙_ : ∀ x {P P′} → P ≡ P′ → x •∙ P ⋉ x •∙ P′
      •_〈_〉∙_ : ∀ x y {P P′} → P ≡ P′ → • x 〈 y 〉∙ P ⋉ • x 〈 y 〉∙ P′

   source : ∀ {Γ} {P P′ : Proc Γ} → P ⋉ P′ → Proc Γ
   source {P = P} _ = P

   target : ∀ {Γ} {P P′ : Proc Γ} → P ⋉ P′ → Proc Γ
   target {P′ = P′} _ = P′

   ⋉-refl : ∀ {Γ} → Reflexive (_⋉_ {Γ})
   ⋉-refl {x = Ο} = Ο
   ⋉-refl {x = x •∙ P} = x •∙ refl
   ⋉-refl {x = • x 〈 y 〉∙ P} = • x 〈 y 〉∙ refl
   ⋉-refl {x = P ➕ Q} = ⋉-refl ➕₁ refl
   ⋉-refl {x = P │ Q} = ⋉-refl │ ⋉-refl
   ⋉-refl {x = ν P} = ν ⋉-refl
   ⋉-refl {x = ! P} = ! ⋉-refl

   ⋉-reflexive : ∀ {Γ} → _≡_ ⇒ _⋉_ {Γ}
   ⋉-reflexive refl = ⋉-refl

   ⋈-to-⋉ : ∀ {Γ} → _⋈_ {Γ} ⇒ _⋉_
   ⋈-to-⋉ (νν-swapᵣ P) = νν-swapᵣ P
   ⋈-to-⋉ (νν-swapₗ P) = νν-swapₗ P
   ⋈-to-⋉ (φ ➕₁ Q) = ⋈-to-⋉ φ ➕₁ Q
   ⋈-to-⋉ (P ➕₂ ψ) = P ➕₂ ⋈-to-⋉ ψ
   ⋈-to-⋉ (φ │₁ Q) = ⋈-to-⋉ φ │ ⋉-reflexive Q
   ⋈-to-⋉ (P │₂ ψ) = ⋉-reflexive P │ ⋈-to-⋉ ψ
   ⋈-to-⋉ (ν φ) = ν ⋈-to-⋉ φ
   ⋈-to-⋉ (! φ) = ! ⋈-to-⋉ φ

   -- Renaming commutes with ⋉. This isn't a Renameable (i.e. a functor from Ren), but rather
   -- the action of such a functor on a 2-cell.
   _*⁼ : ∀ {Γ Γ′ P R} (ρ : Ren Γ Γ′) → P ⋉ R → (ρ *) P ⋉ (ρ *) R
   (ρ *⁼) (νν-swapₗ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapₗ ((suc (suc ρ) *) P)
   (ρ *⁼) (νν-swapᵣ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapᵣ ((suc (suc ρ) *) P)
   -- Compatibility.
   (ρ *⁼) Ο = Ο
   (ρ *⁼) (x •∙ P) = (ρ *) x •∙ cong (suc ρ *) P
   (ρ *⁼) (• x 〈 y 〉∙ P) = • (ρ *) x 〈 (ρ *) y 〉∙ cong (ρ *) P
   (ρ *⁼) (P ➕₁ Q) = (ρ *⁼) P ➕₁ cong (ρ *) Q
   (ρ *⁼) (P ➕₂ Q) = cong (ρ *) P ➕₂ (ρ *⁼) Q
   (ρ *⁼) (P │ Q) = (ρ *⁼) P │ (ρ *⁼) Q
   (ρ *⁼) (ν P) = ν (suc ρ *⁼) P
   (ρ *⁼) (! P) = ! (ρ *⁼) P
