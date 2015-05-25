module StructuralCong.Proc where

   open import SharedModules hiding ([_]; preorder) renaming (sym to ≡-sym; trans to ≡-trans)
   import Relation.Binary.PreorderReasoning

   open import Ext

   open import Name using (Name; _+_)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Proc.Ren
   open import Ren as ᴿ using (Ren; push; suc; swap; Renameable; module Renameable; ᴺren);
      open Renameable ⦃...⦄
   open import Ren.Properties

   -- A subset of the usual pi calculus structural congruence, namely equivalence modulo permutation
   -- of adjacent binders. In the de Bruijn setting this means equating ν (ν P) with ν (ν (swap * P)).
   infix 4 _≈_
   infixl 6 _➕_ _│_
   data _≈_ {Γ} : Proc Γ → Proc Γ → Set where
      -- Structural congruence. We need left and right versions of the rule to prove the lattice isos,
      -- although symmetry is derivable without them.
      νν-swapₗ : ∀ P → ν (ν (swap *) P) ≈ ν (ν P)
      νν-swapᵣ : ∀ P → ν (ν P) ≈ ν (ν (swap *) P)
      -- Compatibility.
      Ο : Ο ≈ Ο
      _•∙_ : ∀ {P R} (x : Name Γ) → P ≈ R → x •∙ P ≈ x •∙ R
      •_〈_〉∙_ : ∀ {P R} (x y : Name Γ) → P ≈ R → • x 〈 y 〉∙ P ≈ • x 〈 y 〉∙ R
      _➕_ : ∀ {P Q R S} → P ≈ R → Q ≈ S → P ➕ Q ≈ R ➕ S
      _│_ : ∀ {P Q R S} → P ≈ R → Q ≈ S → P │ Q ≈ R │ S
      ν_ : ∀ {P R} → P ≈ R → ν P ≈ ν R
      !_ : ∀ {P R} → P ≈ R → ! P ≈ ! R
      -- Symmetry and reflexivity are derivable. (Writing this as ∘ in the paper, with arguments reversed).
      trans : ∀ {P R S} → P ≈ R → R ≈ S → P ≈ S

   source : ∀ {Γ} {P P′ : Proc Γ} → P ≈ P′ → Proc Γ
   source {P = P} _ = P

   target : ∀ {Γ} {P P′ : Proc Γ} → P ≈ P′ → Proc Γ
   target {P′ = P′} _ = P′

   ≈-refl : ∀ {Γ} → Reflexive (_≈_ {Γ})
   ≈-refl {x = Ο} = Ο
   ≈-refl {x = x •∙ P} = x •∙ ≈-refl
   ≈-refl {x = • x 〈 y 〉∙ P} = • x 〈 y 〉∙ ≈-refl
   ≈-refl {x = P ➕ Q} = ≈-refl ➕ ≈-refl
   ≈-refl {x = P │ Q} = ≈-refl │ ≈-refl
   ≈-refl {x = ν P} = ν ≈-refl
   ≈-refl {x = ! P} = ! ≈-refl

   -- Note that symmetry is not sufficient for structural congruence to be an isomorphism.
   ≈-sym : ∀ {Γ} → Symmetric (_≈_ {Γ})
   ≈-sym (νν-swapₗ P) = νν-swapᵣ P
   ≈-sym (νν-swapᵣ P) = νν-swapₗ P
   ≈-sym Ο = Ο
   ≈-sym (x •∙ P) = x •∙ ≈-sym P
   ≈-sym (• x 〈 y 〉∙ P) = • x 〈 y 〉∙ ≈-sym P
   ≈-sym (P ➕ Q) = ≈-sym P ➕ ≈-sym Q
   ≈-sym (P │ Q) = ≈-sym P │ ≈-sym Q
   ≈-sym (ν P) = ν ≈-sym P
   ≈-sym (! P) = ! ≈-sym P
   ≈-sym (trans P P′) = trans (≈-sym P′) (≈-sym P)

   ≈-sym-involutive : ∀ {Γ} {P P′ : Proc Γ} (φ : P ≈ P′) → ≈-sym (≈-sym φ) ≡ φ
   ≈-sym-involutive Ο = refl
   ≈-sym-involutive (x •∙ φ) = cong (λ P → x •∙ P) (≈-sym-involutive φ)
   ≈-sym-involutive (• x 〈 y 〉∙ φ) = cong (λ P → • x 〈 y 〉∙ P) (≈-sym-involutive φ)
   ≈-sym-involutive (φ ➕ ψ) = cong₂ _➕_ (≈-sym-involutive φ) (≈-sym-involutive ψ)
   ≈-sym-involutive (φ │ ψ) = cong₂ _│_ (≈-sym-involutive φ) (≈-sym-involutive ψ)
   ≈-sym-involutive (νν-swapₗ P) = refl
   ≈-sym-involutive (νν-swapᵣ P) = refl
   ≈-sym-involutive (ν φ) = cong ν_ (≈-sym-involutive φ)
   ≈-sym-involutive (! φ) = cong !_ (≈-sym-involutive φ)
   ≈-sym-involutive (trans φ φ′) = cong₂ trans (≈-sym-involutive φ) (≈-sym-involutive φ′)

   ≈-sym-refl : ∀ {Γ} (P : Proc Γ) → ≈-sym (≈-refl {x = P}) ≡ ≈-refl
   ≈-sym-refl Ο = refl
   ≈-sym-refl (x •∙ P) = cong (λ P → x •∙ P) (≈-sym-refl P)
   ≈-sym-refl (• x 〈 y 〉∙ P) = cong (λ P → • x 〈 y 〉∙ P) (≈-sym-refl P)
   ≈-sym-refl (P ➕ Q) = cong₂ (λ P Q → P ➕ Q) (≈-sym-refl P) (≈-sym-refl Q)
   ≈-sym-refl (P │ Q) = cong₂ (λ P Q → P │ Q) (≈-sym-refl P) (≈-sym-refl Q)
   ≈-sym-refl (ν P) = cong (λ P → ν P) (≈-sym-refl P)
   ≈-sym-refl (! P) = cong (λ P → ! P) (≈-sym-refl P)

   ≈-equiv : ∀ {Γ} → IsEquivalence (_≈_ {Γ})
   ≈-equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = trans }

   private
      open module IsEquivalence′ {Γ} = IsEquivalence (≈-equiv {Γ}) public
         hiding (sym; refl) renaming (trans to ≈-trans; reflexive to ≈-reflexive)

   preorder : ∀ {Γ} → Preorder _ _ _
   preorder {Γ} = record {
            Carrier = Proc Γ;
            _≈_ = _≡_;
            _∼_ = _≈_ {Γ};
            isPreorder = record {
                  isEquivalence = {!!};
                  reflexive = {!≡-reflexive!};
                  trans = {!!}
               }
      }

   module ≈-Reasoning where
      module _ {a} {A : Set a} where
         open Relation.Binary.PreorderReasoning preorder public renaming (_≈⟨_⟩_ to _a⟨_⟩_)

   -- Renaming commutes with ≈. This isn't a Renameable (i.e. functor from Ren), but rather
   -- the action of such a functor on a 2-cell.
   _*⁼ : ∀ {Γ Γ′ P R} (ρ : Ren Γ Γ′) → P ≈ R → (ρ *) P ≈ (ρ *) R
   (ρ *⁼) (νν-swapₗ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapₗ ((suc (suc ρ) *) P)
   (ρ *⁼) (νν-swapᵣ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapᵣ ((suc (suc ρ) *) P)
   -- Compatibility.
   (ρ *⁼) Ο = Ο
   (ρ *⁼) (x •∙ P) = (ρ *) x •∙ (suc ρ *⁼) P
   (ρ *⁼) (• x 〈 y 〉∙ P) = • (ρ *) x 〈 (ρ *) y 〉∙ (ρ *⁼) P
   (ρ *⁼) (P ➕ R) = (ρ *⁼) P ➕ (ρ *⁼) R
   (ρ *⁼) (P │ R) = (ρ *⁼) P │ (ρ *⁼) R
   (ρ *⁼) (ν P) = ν (suc ρ *⁼) P
   (ρ *⁼) (! P) = ! (ρ *⁼) P
   -- Transitivity.
   (ρ *⁼) (trans P R) = trans ((ρ *⁼) P) ((ρ *⁼) R)
