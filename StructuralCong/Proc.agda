-- Braiding. TODO: rename accordingly.
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

   -- Synactic equivalence "modulo" a single transposition of adjacent binders. In the de Bruijn setting
   -- this means equating ν (ν P) with ν (ν (swap * P)). Not a congruence, in contrast to the LFMTP 2015 setup.
   infix 4 _≈_
   infixl 6 _➕₁_ _➕₂_ _│₁_
   data _≈_ {Γ} : Proc Γ → Proc Γ → Set where
      -- Braidings. We need left and right versions of the rule to prove the lattice isos, although symmetry is
      -- derivable without them. TODO: revert to a single version of the rule.
      νν-swapₗ : ∀ P → ν (ν (swap *) P) ≈ ν (ν P)
      νν-swapᵣ : ∀ P → ν (ν P) ≈ ν (ν (swap *) P)
      -- Compatibility.
      Ο : Ο ≈ Ο
      _•∙_ : ∀ (x : Name Γ) P → x •∙ P ≈ x •∙ P
      •_〈_〉∙_ : ∀ (x y : Name Γ) P → • x 〈 y 〉∙ P ≈ • x 〈 y 〉∙ P
      _➕₁_ : ∀ {P R} → P ≈ R → ∀ Q → P ➕ Q ≈ R ➕ Q
      _➕₂_ : ∀ {Q S} → ∀ P → Q ≈ S → P ➕ Q ≈ P ➕ S
      _│₁_ : ∀ {P R} → P ≈ R → ∀ Q → P │ Q ≈ R │ Q
      _│₂_ : ∀ {Q S} → ∀ P → Q ≈ S → P │ Q ≈ P │ S
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
   ≈-refl {x = x •∙ P} = x •∙ P
   ≈-refl {x = • x 〈 y 〉∙ P} = • x 〈 y 〉∙ P
   ≈-refl {x = P ➕ Q} = ≈-refl ➕₁ Q
   ≈-refl {x = P │ Q} = ≈-refl │₁ Q
   ≈-refl {x = ν P} = ν ≈-refl
   ≈-refl {x = ! P} = ! ≈-refl

   -- Note that symmetry is not sufficient for structural congruence to be an isomorphism.
   ≈-sym : ∀ {Γ} → Symmetric (_≈_ {Γ})
   ≈-sym (νν-swapₗ P) = νν-swapᵣ P
   ≈-sym (νν-swapᵣ P) = νν-swapₗ P
   ≈-sym Ο = Ο
   ≈-sym (x •∙ P) = x •∙ P
   ≈-sym (• x 〈 y 〉∙ P) = • x 〈 y 〉∙ P
   ≈-sym (P ➕₁ Q) = ≈-sym P ➕₁ Q
   ≈-sym (P ➕₂ Q) = P ➕₂ ≈-sym Q
   ≈-sym (P │₁ Q) = ≈-sym P │₁ Q
   ≈-sym (P │₂ Q) = P │₂ ≈-sym Q
   ≈-sym (ν P) = ν ≈-sym P
   ≈-sym (! P) = ! ≈-sym P
   ≈-sym (trans P P′) = trans (≈-sym P′) (≈-sym P)

   ≈-sym-involutive : ∀ {Γ} {P P′ : Proc Γ} (φ : P ≈ P′) → ≈-sym (≈-sym φ) ≡ φ
   ≈-sym-involutive Ο = refl
   ≈-sym-involutive (x •∙ P) = refl
   ≈-sym-involutive (• x 〈 y 〉∙ φ) = refl
   ≈-sym-involutive (φ ➕₁ Q) = cong (flip _➕₁_ Q) (≈-sym-involutive φ)
   ≈-sym-involutive (P ➕₂ ψ) = cong (_➕₂_ P) (≈-sym-involutive ψ)
   ≈-sym-involutive (φ │₁ Q) = cong (flip _│₁_ Q) (≈-sym-involutive φ)
   ≈-sym-involutive (P │₂ ψ) = cong (_│₂_ P) (≈-sym-involutive ψ)
   ≈-sym-involutive (νν-swapₗ P) = refl
   ≈-sym-involutive (νν-swapᵣ P) = refl
   ≈-sym-involutive (ν φ) = cong ν_ (≈-sym-involutive φ)
   ≈-sym-involutive (! φ) = cong !_ (≈-sym-involutive φ)
   ≈-sym-involutive (trans φ φ′) = cong₂ trans (≈-sym-involutive φ) (≈-sym-involutive φ′)

   ≈-sym-refl : ∀ {Γ} (P : Proc Γ) → ≈-sym (≈-refl {x = P}) ≡ ≈-refl
   ≈-sym-refl Ο = refl
   ≈-sym-refl (x •∙ P) = refl
   ≈-sym-refl (• x 〈 y 〉∙ P) = refl
   ≈-sym-refl (P ➕ Q) = cong (flip _➕₁_ Q) (≈-sym-refl P)
   ≈-sym-refl (P │ Q) = cong (flip _│₁_ Q) (≈-sym-refl P)
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
            isEquivalence = isEquivalence;
            reflexive = λ { {i} {.i} refl → ≈-refl };
            trans = ≈-trans
         }
      }

   module ≈-Reasoning {Γ} where
      module _ where
         open Relation.Binary.PreorderReasoning (preorder {Γ}) public renaming (_∼⟨_⟩_ to _≈⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

   -- Renaming commutes with ≈. This isn't a Renameable (i.e. functor from Ren), but rather
   -- the action of such a functor on a 2-cell.
   _*⁼ : ∀ {Γ Γ′ P R} (ρ : Ren Γ Γ′) → P ≈ R → (ρ *) P ≈ (ρ *) R
   (ρ *⁼) (νν-swapₗ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapₗ ((suc (suc ρ) *) P)
   (ρ *⁼) (νν-swapᵣ P) with ᴾ.ν (ν (swap *) ((suc (suc ρ) *) P))
   ... | P′ rewrite ≡-sym (swap-suc-suc ρ P) = νν-swapᵣ ((suc (suc ρ) *) P)
   -- Compatibility.
   (ρ *⁼) Ο = Ο
   (ρ *⁼) (x •∙ P) = (ρ *) x •∙ (suc ρ *) P
   (ρ *⁼) (• x 〈 y 〉∙ P) = • (ρ *) x 〈 (ρ *) y 〉∙ (ρ *) P
   (ρ *⁼) (P ➕₁ Q) = (ρ *⁼) P ➕₁ (ρ *) Q
   (ρ *⁼) (P ➕₂ Q) = (ρ *) P ➕₂ (ρ *⁼) Q
   (ρ *⁼) (P │₁ Q) = (ρ *⁼) P │₁ (ρ *) Q
   (ρ *⁼) (P │₂ Q) = (ρ *) P │₂ (ρ *⁼) Q
   (ρ *⁼) (ν P) = ν (suc ρ *⁼) P
   (ρ *⁼) (! P) = ! (ρ *⁼) P
   -- Transitivity.
   (ρ *⁼) (trans P R) = trans ((ρ *⁼) P) ((ρ *⁼) R)
