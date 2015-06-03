module Transition.Concur2 where

   open import SharedModules hiding ([_])

   open import Ext

   open import Action as ᴬ
      using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc; _ᴬ⌣_; ᴬ⌣-sym; ᴬ⌣-sym-involutive; ᴺinc-inc);
      open ᴬ.Actionᵇ; open ᴬ.Actionᶜ; open ᴬ._ᴬ⌣_
   import Action.Ren
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; ᴺren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Second component here abstracts over the two action constructors.
   ᴬΔ : ∀ {Γ} {a a′ : Action Γ} → a ᴬ⌣ a′ → Σ[ A ∈ Set ] (A → Action (Γ + inc a))
   ᴬΔ {Γ} ᵛ∇ᵛ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᵇ∇ᵇ = Actionᵇ (Γ + 1) , _ᵇ
   ᴬΔ {Γ} ᵇ∇ᶜ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᶜ∇ᵇ = Actionᵇ Γ , _ᵇ
   ᴬΔ {Γ} ᶜ∇ᶜ = Actionᶜ Γ , _ᶜ

   -- The residual a′/a. Note that ᵇ∇ᵇ may also relate two bound outputs, but only if they represent
   -- extrusions of distinct binders.
   ᴬ/ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → π₁ (ᴬΔ a⌣a′)
   ᴬ/ (ᵛ∇ᵛ {u = u}) = • ᴺ.suc u 〈 zero 〉
   ᴬ/ (ᵇ∇ᵇ {a′ = a′}) = (push *) a′
   ᴬ/ (ᵇ∇ᶜ {a′ = a′}) = (push *) a′
   ᴬ/ (ᶜ∇ᵇ {a′ = a′}) = a′
   ᴬ/ (ᶜ∇ᶜ {a′ = a′}) = a′

   -- Symmetrise.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Action (Γ + inc a) × Action (Γ + inc a′)
   ᴬ⊖ a⌣a′ = π₂ (ᴬΔ a⌣a′) (ᴬ/ a⌣a′) , π₂ (ᴬΔ (ᴬ⌣-sym a⌣a′)) (ᴬ/ (ᴬ⌣-sym a⌣a′))

   -- A pair of composable actions.
   Action₂ : Cxt → Set
   Action₂ Γ = Σ[ a ∈ Action Γ ] Action (Γ + inc a)

   inc₂ : ∀ {Γ} → Action₂ Γ → Cxt
   inc₂ (a , a′) = inc a + inc a′

   inc₂-def : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Γ + inc₂ (a , π₁ (ᴬ⊖ a⌣a′)) ≡ Γ + inc a + inc (π₁ (ᴬ⊖ a⌣a′))
   inc₂-def ᵛ∇ᵛ = refl
   inc₂-def ᵇ∇ᵇ = refl
   inc₂-def ᵇ∇ᶜ = refl
   inc₂-def ᶜ∇ᵇ = refl
   inc₂-def ᶜ∇ᶜ = refl

   -- Cofinality of action residuals is simply agreement on target context.
   ᴬ⊖-✓ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Γ + inc a + inc (π₁ (ᴬ⊖ a⌣a′)) ≡ Γ + inc a′ + inc (π₂ (ᴬ⊖ a⌣a′))
   ᴬ⊖-✓ ᵛ∇ᵛ = refl
   ᴬ⊖-✓ ᵇ∇ᵇ = refl
   ᴬ⊖-✓ ᵇ∇ᶜ = refl
   ᴬ⊖-✓ ᶜ∇ᵇ = refl
   ᴬ⊖-✓ ᶜ∇ᶜ = refl

   -- Whether two coinitial evaluation contexts are concurrent; define symmetric reduction and then close under
   -- symmetry. Convenient to have this indexed by the kind of action residual. TODO: cases for •│ and ᵥ│.
   syntax Concur E E′ a⌣a′ = E ⌣[ a⌣a′ ] E′
   syntax Concur₁ E E′ a′/a = E ⌣₁[ a′/a ] E′
   infix 4 Concur₁

   data Concur {Γ} : ∀ {a a′ : Action Γ} {P R R′}
               (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → a ᴬ⌣ a′ → Set where

   data Concur₁ {Γ} : ∀ {a a′ : Action Γ} {P R R′} →
                P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → a ᴬ⌣ a′ → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᵇ ] P │ᵇ F
      _ᵇ│ᶜ_ : ∀ {P Q R S} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F
      _ᶜ│ᵇ_ : ∀ {P Q R S} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᵇ ] P │ᵇ F
      _ᶜ│ᶜ_ : ∀ {P Q R S} {a a′ : Actionᶜ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F
      -- │ᵇ• might be a better naming convention here, and similarly for │ᵇᵥ.
      _│•ᵇ_ : ∀ {x y P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣[ ᵇ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │• F
      _│•ᶜ_ : ∀ {x y P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣[ ᶜ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │• F
      _ᵇ│•_ : ∀ {x y P Q R S S′} {a : Actionᵇ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │• F′
      _ᶜ│•_ : ∀ {x y P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │• F′
      _│ᵥᵇ_ : ∀ {x P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
             E ⌣[ ᵇ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │ᵥ F
      _│ᵥᶜ_ : ∀ {x P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣[ ᶜ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F
      _ᵇ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │ᵥ F′
      _ᶜ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣[ ᶜ∇ᵇ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │ᵥ F′
      _➕₁_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
             E ⌣[ a⌣a′ ] E′ → (Q : Proc Γ) → E ➕₁ Q ⌣₁[ a⌣a′ ] E′ ➕₁ Q
      _│ᵇᵇ_ : ∀ {Q S S′} {a a′ : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᵇ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ a⌣a′ ] P │ᵇ F′
      _│ᵇᶜ_ : ∀ {Q S S′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F′
      _│ᶜᶜ_ : ∀ {Q S S′} {a a′ : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F′
      _ᵇᵇ│_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a⌣a′} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′} →
              E ⌣[ a⌣a′ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ a⌣a′ ] E′ ᵇ│ Q
      _ᵇᶜ│_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣[ ᵇ∇ᶜ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ ᶜ│ Q
      _ᶜᶜ│_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣[ ᶜ∇ᶜ ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ ᶜ│ Q
      _│•_ : ∀ {x y u z P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ • u 〈 z 〉 ᶜ - _ ]→ S′} →
             E ⌣[ ᵇ∇ᵇ ] E′ → F ⌣[ ᶜ∇ᶜ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │• F′
      _│ᵥ•_ : ∀ {x u y P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ • u 〈 y 〉 ᶜ - _ ]→ S′} →
             E ⌣[ ᵇ∇ᵇ ] E′ → F ⌣[ ᵇ∇ᶜ ] F′ → E │ᵥ F ⌣₁[ ᶜ∇ᶜ ] E′ │• F′
      _│ᵥ_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {•x⌣•u} {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣[ ᵇ∇ᵇ ] E′ → F ⌣[ •x⌣•u ] F′ → E │ᵥ F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      ν•_ : ∀ {x u P R R′} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ • ᴺ.suc u 〈 zero 〉 ᶜ - _ ]→ R′} →
            E ⌣[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵛ∇ᵛ ] ν• E′
      ν•ᵇ_ : ∀ {x P R R′} {a : Actionᵇ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᵇ - _ ]→ R′} →
            E ⌣[ ᶜ∇ᵇ ] E′ → ν• E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      ν•ᶜ_ : ∀ {x P R R′} {a : Actionᶜ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᶜ - _ ]→ R′} →
            E ⌣[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᵇᵇ_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᵇ - _ ]→ R′} →
          E ⌣[ ᵇ∇ᵇ ] E′ → νᵇ E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      νᵛᵛ_ : ∀ {P R R′} {x u : Name Γ} {E : P —[ (• (push *) x) ᵇ - _ ]→ R} {E′ : P —[ (• (push *) u) ᵇ - _ ]→ R′} →
          E ⌣[ ᵛ∇ᵛ ] E′ → νᵇ E ⌣₁[ ᵛ∇ᵛ ] νᵇ E′
      νᵇᶜ_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣[ ᵇ∇ᶜ ] E′ → νᵇ E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᶜᶜ_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ (push *) a ᶜ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣[ ᶜ∇ᶜ ] E′ → νᶜ E ⌣₁[ ᶜ∇ᶜ ] νᶜ E′
      !_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P │ ! P —[ a - _ ]→ R} {E′ : P │ ! P —[ a′ - _ ]→ R′} →
           E ⌣[ a⌣a′ ] E′ → ! E ⌣₁[ a⌣a′ ] ! E′
