module Transition.Concur where

   open import ProofRelevantPiCommon hiding ([_])
   open import Ext

   open import Action as ᴬ
      using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⌣-sym; ᴬ⌣-sym-involutive; ᴬ⊖); open _ᴬ⌣_
   import Action.Ren
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_)
   open import Ren as ᴿ using (Ren; Renameable; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; tgt); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Whether two coinitial evaluation contexts are concurrent; define asymmetrically and then close under symmetry.
   syntax Concur₁ E E′ a′/a = E ⌣₁[ a′/a ] E′
   infix 4 Concur₁

   data Concur₁ {Γ} : ∀ {a a′ : Action Γ} {P R R′} → P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → a ᴬ⌣ a′ → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᵇ ] P │ᵇ F
      _ᵇ│ᶜ_ : ∀ {P Q R S} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F
      _ᶜ│ᵇ_ : ∀ {P Q R S} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᵇ ] P │ᵇ F
      _ᶜ│ᶜ_ : ∀ {P Q R S} {a a′ : Actionᶜ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F
      -- │ᵇ• might be a better naming convention here, and similarly for │ᵇᵥ. Or swap with ᵇ│•?
      _│•ᵇ_ : ∀ {x y P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᵇ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │• F
      _│•ᶜ_ : ∀ {x y P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │• F
      _ᵇ│•_ : ∀ {x y P Q R S S′} {a : Actionᵇ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │• F′
      _ᶜ│•_ : ∀ {x y P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │• F′
      _│ᵥᵇ_ : ∀ {x P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │ᵥ F
      _│ᵥᶜ_ : ∀ {x P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F
      _ᵇ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᵇ Γ} {𝑎} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ 𝑎 ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │ᵥ F′
      _ᶜ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᶜ∇ᵇ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │ᵥ F′
      _➕₁_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {𝑎} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
             E ⌣₁[ 𝑎 ] E′ → (Q : Proc Γ) → E ➕₁ Q ⌣₁[ 𝑎 ] E′ ➕₁ Q
      _│ᵇᵇ_ : ∀ {Q S S′} {a a′ : Actionᵇ Γ} {𝑎} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᵇ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ 𝑎 ] F′ → P │ᵇ F ⌣₁[ 𝑎 ] P │ᵇ F′
      _│ᵇᶜ_ : ∀ {Q S S′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F′
      _│ᶜᶜ_ : ∀ {Q S S′} {a a′ : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F′
      _│ᵛᵛ_ : ∀ {Q S S′} {F : Q —[ τ ᶜ - _ ]→ S} {F′ : Q —[ τ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᵛ∇ᵛ ] F′ → P │ᶜ F ⌣₁[ ᵛ∇ᵛ ] P │ᶜ F′
      _ᵇᵇ│_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {𝑎} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′} →
              E ⌣₁[ 𝑎 ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ 𝑎 ] E′ ᵇ│ Q
      _ᵇᶜ│_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᵇ∇ᶜ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ ᶜ│ Q
      _ᶜᶜ│_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᶜ ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ ᶜ│ Q
      _ᵛᵛ│_ : ∀ {P R R′} {E : P —[ τ ᶜ - _ ]→ R} {E′ : P —[ τ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᵛ∇ᵛ ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ ᵛ∇ᵛ ] E′ ᶜ│ Q
      _│•_ : ∀ {x y u z P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ • u 〈 z 〉 ᶜ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᶜ∇ᶜ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │• F′
      _│•ᵥ_ : ∀ {x u y P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
              {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
              E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᶜ∇ᵇ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      _│ᵥ_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ˣ∇ˣ ] F′ → E │ᵥ F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      -- TODO: better name.
      _│ᵥ′_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᵇ∇ᵇ ] F′ → E │ᵥ F ⌣₁[ ᵛ∇ᵛ ] E′ │ᵥ F′
      ν•_ : ∀ {x u P R R′} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ • ᴺ.suc u 〈 zero 〉 ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ˣ∇ˣ ] ν• E′
      ν•ᵇ_ : ∀ {x P R R′} {a : Actionᵇ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᵇ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᵇ ] E′ → ν• E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      ν•ᶜ_ : ∀ {x P R R′} {a : Actionᶜ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᵇᵇ_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᵇ - _ ]→ R′} →
            E ⌣₁[ ᵇ∇ᵇ ] E′ → νᵇ E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      νˣˣ_ : ∀ {P R R′} {x u : Name Γ} {E : P —[ (• ᴺ.suc x) ᵇ - _ ]→ R} {E′ : P —[ (• ᴺ.suc u) ᵇ - _ ]→ R′} →
            E ⌣₁[ ˣ∇ˣ ] E′ → νᵇ E ⌣₁[ ˣ∇ˣ ] νᵇ E′
      νᵇᶜ_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
            E ⌣₁[ ᵇ∇ᶜ ] E′ → νᵇ E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᶜᶜ_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ (push *) a ᶜ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → νᶜ E ⌣₁[ ᶜ∇ᶜ ] νᶜ E′
      νᵛᵛ_ : ∀ {P R R′} {E : P —[ τ ᶜ - _ ]→ R} {E′ : P —[ τ ᶜ - _ ]→ R′} → E ⌣₁[ ᵛ∇ᵛ ] E′ → νᶜ E ⌣₁[ ᵛ∇ᵛ ] νᶜ E′
      !_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {𝑎} {R R′} {E : P │ ! P —[ a - _ ]→ R} {E′ : P │ ! P —[ a′ - _ ]→ R′} →
           E ⌣₁[ 𝑎 ] E′ → ! E ⌣₁[ 𝑎 ] ! E′

   syntax Concur E E′ 𝑎 = E ⌣[ 𝑎 ] E′

   Concur : ∀ {Γ} {a a′ : Action Γ} {P R R′}
            (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → a ᴬ⌣ a′ → Set
   Concur E E′ 𝑎 = E ⌣₁[ 𝑎 ] E′ ⊎ E′ ⌣₁[ ᴬ⌣-sym 𝑎 ] E

   ⌣-sym : ∀ {Γ} {P : Proc Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} →
           {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} → E ⌣[ 𝑎 ] E′ → E′ ⌣[ ᴬ⌣-sym 𝑎 ] E
   ⌣-sym (inj₁ 𝐸) = inj₂ (subst (Concur₁ _ _) (sym (ᴬ⌣-sym-involutive _)) 𝐸)
   ⌣-sym (inj₂ 𝐸) = inj₁ 𝐸

   -- The type of the symmetric residual of concurrent transitions E and E′.
   record Delta′ {Γ P} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {R R′}
                (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) : Set where
      constructor Delta
      a′/a = π₁ (ᴬ⊖ 𝑎)
      a/a′ = π₂ (ᴬ⊖ 𝑎)
      field
         -- Cofinality of action residuals isn't baked in, so need to coerce tgt₁ and tgt₂ to same type.
         {tgt₁ tgt₂} : _
         E′/E : R —[ a′/a - _ ]→ tgt₁
         E/E′ : R′ —[ a/a′ - _ ]→ tgt₂

   infixl 5 Delta
   syntax Delta E E′ = E ᵀΔ E′
   syntax Delta′ 𝑎 E E′ = E Δ′[ 𝑎 ] E′

   open import Ren.Properties
   open Delta′

   -- The symmetric residual (E′/E , E/E′).
   ⊖₁ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
        E ⌣₁[ 𝑎 ] E′ → E Δ′[ 𝑎 ] E′
   ⊖₁ (E ᵇ│ᵇ F) = tgt E │ᵇ (push *ᵇ) F ᵀΔ (push *ᵇ) E ᵇ│ tgt F
   ⊖₁ (E ᵇ│ᶜ F) = tgt E │ᶜ (push *ᶜ) F ᵀΔ E ᵇ│ tgt F
   ⊖₁ (E ᶜ│ᵇ F) = tgt E │ᵇ F ᵀΔ (push *ᶜ) E ᶜ│ tgt F
   ⊖₁ (E ᶜ│ᶜ F) = tgt E │ᶜ F ᵀΔ E ᶜ│ tgt F
   -- These two cases use explicit substitutions; with/rewrite clauses caused complications later, but probably know
   -- how to deal with that now.
   ⊖₁ (_│•ᵇ_ {y = y} {a = a} {E′ = E′} 𝐸 F) =
      E′/E (⊖₁ 𝐸) │• (push *ᶜ) F ᵀΔ
      subst (λ a → _ —[ a ᵇ - _ ]→ (suc (pop y) *) (tgt₂ (⊖₁ 𝐸))) (pop∘push y a) ((pop y *ᵇ) (E/E′ (⊖₁ 𝐸))) ᵇ│ tgt F
   ⊖₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) =
      E′/E (⊖₁ 𝐸) │• F ᵀΔ
      subst (λ a → _ —[ a ᶜ - _ ]→ (pop y *) (tgt₂ (⊖₁ 𝐸))) (pop∘push y a) ((pop y *ᶜ) (E/E′ (⊖₁ 𝐸))) ᶜ│ tgt F
   ⊖₁ (_ᵇ│•_ {y = y} E 𝐹) = (push *ᵇ) E ᵀ.│• E′/E (⊖₁ 𝐹) ᵀΔ (pop y *) (tgt E) │ᵇ E/E′ (⊖₁ 𝐹)
   ⊖₁ (_ᶜ│•_ {y = y} E 𝐹) = E │• E′/E (⊖₁ 𝐹) ᵀΔ (pop y *) (tgt E) │ᶜ E/E′ (⊖₁ 𝐹)
   ⊖₁ (_│ᵥᵇ_ {a = a} 𝐸 F) with (id *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | id*E/E′ rewrite *-preserves-id ((push *) a) = E′/E (⊖₁ 𝐸) │ᵥ (push *ᵇ) F ᵀΔ νᵇ (id*E/E′ ᵇ│ tgt F)
   ⊖₁ (_│ᵥᶜ_ {a = a} 𝐸 F) with (id *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | id*E/E′ rewrite *-preserves-id ((push *) a) = E′/E (⊖₁ 𝐸) │ᵥ F ᵀΔ νᶜ (id*E/E′ ᶜ│ tgt F)
   ⊖₁ (_ᵇ│ᵥ_ {𝑎 = ˣ∇ˣ} E 𝐹) = (push *ᵇ) E │• E′/E (⊖₁ 𝐹) ᵀΔ ν• ((id *) (tgt E) │ᶜ E/E′ (⊖₁ 𝐹))
   ⊖₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) = (push *ᵇ) E │ᵥ E′/E (⊖₁ 𝐹) ᵀΔ νᵇ ((id *) (tgt E) │ᵇ E/E′ (⊖₁ 𝐹))
   ⊖₁ (E ᶜ│ᵥ 𝐹) = E │ᵥ E′/E (⊖₁ 𝐹) ᵀΔ νᶜ ((id *) (tgt E ) │ᶜ E/E′ (⊖₁ 𝐹))
   ⊖₁ (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} P 𝐹) = (push *) P │ᶜ E′/E (⊖₁ 𝐹) ᵀΔ (push *) P │ᶜ E/E′ (⊖₁ 𝐹)
   ⊖₁ (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) = (push *) P │ᵇ E′/E (⊖₁ 𝐹) ᵀΔ (push *) P │ᵇ E/E′ (⊖₁ 𝐹)
   ⊖₁ (P │ᵇᶜ 𝐹) = (push *) P │ᶜ E′/E (⊖₁ 𝐹) ᵀΔ P │ᵇ E/E′ (⊖₁ 𝐹)
   ⊖₁ (P │ᶜᶜ 𝐹) = P │ᶜ E′/E (⊖₁ 𝐹) ᵀΔ P │ᶜ E/E′ (⊖₁ 𝐹)
   ⊖₁ (P │ᵛᵛ 𝐹) = P │ᶜ E′/E (⊖₁ 𝐹) ᵀΔ P │ᶜ E/E′ (⊖₁ 𝐹)
   ⊖₁ (_ᵇᵇ│_ {𝑎 = ˣ∇ˣ} 𝐸 Q) = E′/E (⊖₁ 𝐸) ᶜ│ (push *) Q ᵀΔ E/E′ (⊖₁ 𝐸) ᶜ│ (push *) Q
   ⊖₁ (_ᵇᵇ│_ {𝑎 = ᵇ∇ᵇ} 𝐸 Q) = E′/E (⊖₁ 𝐸) ᵇ│ (push *) Q ᵀΔ E/E′ (⊖₁ 𝐸) ᵇ│ (push *) Q
   ⊖₁ (𝐸 ᵇᶜ│ Q) = E′/E (⊖₁ 𝐸) ᶜ│ (push *) Q ᵀΔ E/E′ (⊖₁ 𝐸) ᵇ│ Q
   ⊖₁ (𝐸 ᶜᶜ│ Q) = E′/E (⊖₁ 𝐸) ᶜ│ Q ᵀΔ E/E′ (⊖₁ 𝐸) ᶜ│ Q
   ⊖₁ (𝐸 ᵛᵛ│ Q) = E′/E (⊖₁ 𝐸) ᶜ│ Q ᵀΔ E/E′ (⊖₁ 𝐸) ᶜ│ Q
   ⊖₁ (𝐸 ➕₁ F) = E′/E (⊖₁ 𝐸) ᵀΔ E/E′ (⊖₁ 𝐸)
   ⊖₁ (_│•_ {x = x} {y} {u} {z} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸)) | (pop z *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E′/E | pop-z*E/E′ =
      pop-y*E′/E │• E′/E (⊖₁ 𝐹) ᵀΔ pop-z*E/E′ │• E/E′ (⊖₁ 𝐹)
   ⊖₁ (_│•ᵥ_ {u = u} {y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | pop-y*E′/E = pop-y*E′/E │ᵥ E′/E (⊖₁ 𝐹) ᵀΔ νᶜ ((id *ᵇ) (E/E′ (⊖₁ 𝐸)) │• E/E′ (⊖₁ 𝐹))
   ⊖₁ (𝐸 │ᵥ 𝐹) = νᶜ ((id *ᵇ) (E′/E (⊖₁ 𝐸)) │• E′/E (⊖₁ 𝐹)) ᵀΔ νᶜ ((id *ᵇ) (E/E′ (⊖₁ 𝐸)) │• E/E′ (⊖₁ 𝐹))
   ⊖₁ (𝐸 │ᵥ′ 𝐹) = νᶜ ((id *ᵇ) (E′/E (⊖₁ 𝐸)) │ᵥ E′/E (⊖₁ 𝐹)) ᵀΔ νᶜ ((id *ᵇ) (E/E′ (⊖₁ 𝐸)) │ᵥ E/E′ (⊖₁ 𝐹))
   ⊖₁ (ν• 𝐸) = E′/E (⊖₁ 𝐸) ᵀΔ E/E′ (⊖₁ 𝐸)
   ⊖₁ (ν•ᵇ_ {x = x} {a = a} 𝐸) = E′/E (⊖₁ 𝐸) ᵀΔ ν• (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ⊖₁ (ν•ᶜ 𝐸) = E′/E (⊖₁ 𝐸) ᵀΔ ν• E/E′ (⊖₁ 𝐸)
   ⊖₁ (νᵇᵇ_ {a = x •} {a} 𝐸) with (swap *ᵇ) (E/E′ (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push a = νᵇ swap*E′/E ᵀΔ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {u •} 𝐸) with (swap *ᵇ) (E/E′ (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | swap*E/E′ | swap*E′/E = νᵇ swap*E′/E ᵀΔ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {• u} 𝐸) = νᵇ (swap *ᵇ) (E′/E (⊖₁ 𝐸)) ᵀΔ νᵇ (swap *ᵇ) (E/E′ (⊖₁ 𝐸))
   ⊖₁ (νˣˣ 𝐸) = νᶜ (swap *ᶜ) (E′/E (⊖₁ 𝐸)) ᵀΔ νᶜ (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ⊖₁ (νᵇᶜ_ {a′ = a′} 𝐸) with (swap *ᶜ) (E′/E (⊖₁ 𝐸))
   ... | swap*E′/E rewrite swap∘push∘push a′ = νᶜ swap*E′/E ᵀΔ νᵇ E/E′ (⊖₁ 𝐸)
   ⊖₁ (νᶜᶜ 𝐸) = νᶜ (E′/E (⊖₁ 𝐸)) ᵀΔ νᶜ (E/E′ (⊖₁ 𝐸))
   ⊖₁ (νᵛᵛ 𝐸) = νᶜ (E′/E (⊖₁ 𝐸)) ᵀΔ νᶜ (E/E′ (⊖₁ 𝐸))
   ⊖₁ (! 𝐸) = E′/E (⊖₁ 𝐸) ᵀΔ E/E′ (⊖₁ 𝐸)

   -- Now symmetrise.
   ⊖ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
       E ⌣[ 𝑎 ] E′ → E Δ′[ 𝑎 ] E′
   ⊖ (inj₁ 𝐸) = ⊖₁ 𝐸
   ⊖ {𝑎 = 𝑎} (inj₂ 𝐸′) with ⊖₁ 𝐸′
   ⊖ {𝑎 = ˣ∇ˣ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′
   ⊖ {𝑎 = ᵇ∇ᵇ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′
   ⊖ {𝑎 = ᵇ∇ᶜ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′
   ⊖ {𝑎 = ᶜ∇ᵇ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′
   ⊖ {𝑎 = ᶜ∇ᶜ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′
   ⊖ {𝑎 = ᵛ∇ᵛ} (inj₂ 𝐸′) | E/E′ ᵀΔ E′/E = E′/E ᵀΔ E/E′

   module Properties {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
      (𝐸 : E ⌣[ 𝑎 ] E′) where

      postulate
         ⊖-preserves-sym : E′/E (⊖ 𝐸) ≅ E/E′ (⊖ (⌣-sym 𝐸))
         ⊖-preserves-sym′ : tgt₂ (⊖ 𝐸) ≡ tgt₁ (⊖ (⌣-sym 𝐸))
