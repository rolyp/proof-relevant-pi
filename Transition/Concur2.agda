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

   data Concur {Γ} : ∀ {a a′ : Action Γ} {P R R′} (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → a ᴬ⌣ a′ → Set
   data Concur₁ {Γ} : ∀ {a a′ : Action Γ} {P R R′} → P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → a ᴬ⌣ a′ → Set

   data Concur {Γ} where
      [_] : ∀ {a a′ : Action Γ} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {a⌣a′ : a ᴬ⌣ a′} →
            E ⌣₁[ a⌣a′ ] E′ → E ⌣[ a⌣a′ ] E′
      [_]ˡ : ∀ {a a′ : Action Γ} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {a⌣a′ : a ᴬ⌣ a′} →
            E ⌣₁[ a⌣a′ ] E′ → E′ ⌣[ ᴬ⌣-sym a⌣a′ ] E

   data Concur₁ {Γ} where
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

   -- Flip the bit which says which way around to read the constructor.
   ⌣-sym : ∀ {Γ} {a a′ : Action Γ} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {a⌣a′ : a ᴬ⌣ a′} →
           E ⌣[ a⌣a′ ] E′ → E′ ⌣[ ᴬ⌣-sym a⌣a′ ] E
   ⌣-sym [ 𝐸 ] = [ 𝐸 ]ˡ
   ⌣-sym [ 𝐸 ]ˡ = [ subst (Concur₁ _ _) (sym (ᴬ⌣-sym-involutive _)) 𝐸 ]

   -- The type of the symmetric residual of concurrent transitions E and E′. Because cofinality of action
   -- residuals isn't baked in, need to coerce targets of E/E′ and E′/E to the same type.
   record Delta′ {Γ P} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) {R R′}
                (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) : Set where
      constructor Delta
      a′/a = π₁ (ᴬ⊖ a⌣a′)
      a/a′ = π₂ (ᴬ⊖ a⌣a′)
      Γ′ = Γ + inc₂ (a , a′/a)
      field
         {S S′} : Proc Γ′
         E′/E : R —[ a′/a - _ ]→ subst Proc (inc₂-def a⌣a′) S
         E/E′ : R′ —[ a/a′ - _ ]→ subst Proc (trans (inc₂-def a⌣a′) (ᴬ⊖-✓ a⌣a′)) S′

   infixl 5 Delta
   syntax Delta E E′ = E ᵀΔ E′
   syntax Delta′ a⌣a′ E E′ = E Δ′[ a⌣a′ ] E′

   open import Ren.Properties
   open Delta′

   -- The symmetric residual (E′/E , E/E′). The paper defines the residual using E and E′, with E ⌣ E′
   -- implicit; here we work directly with the proof of E ⌣ E′ and leave E and E′ implicit.
   ⊖₁ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
        E ⌣₁[ a⌣a′ ] E′ → E Δ′[ a⌣a′ ] E′
   ⊖ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
       E ⌣[ a⌣a′ ] E′ → E Δ′[ a⌣a′ ] E′

   ⊖₁ (E ᵇ│ᵇ F) = target E │ᵇ (push *ᵇ) F ᵀΔ (push *ᵇ) E ᵇ│ target F
   ⊖₁ (E ᵇ│ᶜ F) = target E │ᶜ (push *ᶜ) F ᵀΔ E ᵇ│ target F
   ⊖₁ (E ᶜ│ᵇ F) = target E │ᵇ F ᵀΔ (push *ᶜ) E ᶜ│ target F
   ⊖₁ (E ᶜ│ᶜ F) = target E │ᶜ F ᵀΔ E ᶜ│ target F
   ⊖₁ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) with (pop y *ᵇ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖ 𝐸) │• (push *ᶜ) F ᵀΔ pop-y*E/E′ ᵇ│ target F
   ⊖₁ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) with (pop y *ᶜ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖ 𝐸) │• F ᵀΔ pop-y*E/E′ ᶜ│ target F
   ⊖₁ (_ᵇ│•_ {y = y} E 𝐹) = (push *ᵇ) E ᵀ.│• E′/E (⊖ 𝐹) ᵀΔ (pop y *) (target E) │ᵇ E/E′ (⊖ 𝐹)
   ⊖₁ (_ᶜ│•_ {y = y} E 𝐹) = E │• E′/E (⊖ 𝐹) ᵀΔ (pop y *) (target E) │ᶜ E/E′ (⊖ 𝐹)
   ⊖₁ (𝐸 │ᵥᵇ F) = E′/E (⊖ 𝐸) │ᵥ (push *ᵇ) F ᵀΔ νᵇ (E/E′ (⊖ 𝐸) ᵇ│ target F)
   ⊖₁ (𝐸 │ᵥᶜ F) = E′/E (⊖ 𝐸) │ᵥ F ᵀΔ νᶜ (E/E′ (⊖ 𝐸) ᶜ│ target F)
   ⊖₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) with (push *ᵇ) E
   ... | push*E = push*E │• E′/E (⊖ 𝐹) ᵀΔ ν• (target E │ᶜ E/E′ (⊖ 𝐹))
   ⊖₁ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) = (push *ᵇ) E │ᵥ E′/E (⊖ 𝐹) ᵀΔ νᵇ (target E │ᵇ E/E′ (⊖ 𝐹))
   ⊖₁ (E ᶜ│ᵥ 𝐹) = E │ᵥ E′/E (⊖ 𝐹) ᵀΔ νᶜ (target E │ᶜ E/E′ (⊖ 𝐹))
   ⊖₁ (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹) = (push *) P │ᶜ E′/E (⊖ 𝐹) ᵀΔ (push *) P │ᶜ E/E′ (⊖ 𝐹)
   ⊖₁ (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹) = (push *) P │ᵇ E′/E (⊖ 𝐹) ᵀΔ (push *) P │ᵇ E/E′ (⊖ 𝐹)
   ⊖₁ (P │ᵇᶜ 𝐹) = (push *) P │ᶜ E′/E (⊖ 𝐹) ᵀΔ P │ᵇ E/E′ (⊖ 𝐹)
   ⊖₁ (P │ᶜᶜ 𝐹) = P │ᶜ E′/E (⊖ 𝐹) ᵀΔ P │ᶜ E/E′ (⊖ 𝐹)
   ⊖₁ (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸 Q) = E′/E (⊖ 𝐸) ᶜ│ (push *) Q ᵀΔ E/E′ (⊖ 𝐸) ᶜ│ (push *) Q
   ⊖₁ (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸 Q) = E′/E (⊖ 𝐸) ᵇ│ (push *) Q ᵀΔ E/E′ (⊖ 𝐸) ᵇ│ (push *) Q
   ⊖₁ (𝐸 ᵇᶜ│ Q) = E′/E (⊖ 𝐸) ᶜ│ (push *) Q ᵀΔ E/E′ (⊖ 𝐸) ᵇ│ Q
   ⊖₁ (𝐸 ᶜᶜ│ Q) = E′/E (⊖ 𝐸) ᶜ│ Q ᵀΔ E/E′ (⊖ 𝐸) ᶜ│ Q
   ⊖₁ (𝐸 ➕₁ F) = E′/E (⊖ 𝐸) ᵀΔ E/E′ (⊖ 𝐸)
   ⊖₁ (_│•_ {x = x} {y} {u} {z} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖ 𝐸)) | (pop z *ᵇ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E′/E | pop-z*E/E′ rewrite pop∘push u y | pop∘push x z = pop-y*E′/E │• E′/E (⊖ 𝐹) ᵀΔ pop-z*E/E′ │• E/E′ (⊖ 𝐹)
   ⊖₁ (_│ᵥ•_ {x = x} {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push x y = νᶜ (E′/E (⊖ 𝐸) │• E′/E (⊖ 𝐹)) ᵀΔ pop-y*E/E′ │ᵥ E/E′ (⊖ 𝐹)
   ⊖₁ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) = νᶜ (E′/E (⊖ 𝐸) │• E′/E (⊖ 𝐹)) ᵀΔ νᶜ (E/E′ (⊖ 𝐸) │• E/E′ (⊖ 𝐹))
   ⊖₁ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) = νᶜ (E′/E (⊖ 𝐸) │ᵥ E′/E (⊖ 𝐹)) ᵀΔ νᶜ (E/E′ (⊖ 𝐸) │ᵥ E/E′ (⊖ 𝐹))
   ⊖₁ (ν• 𝐸) = E′/E (⊖ 𝐸) ᵀΔ E/E′ (⊖ 𝐸)
   ⊖₁ (ν•ᵇ_ {x = x} {a = a} 𝐸) with (swap *ᶜ) (E/E′ (⊖ 𝐸))
   ... | swap*E/E′ = E′/E (⊖ 𝐸) ᵀΔ ν• swap*E/E′
   ⊖₁ (ν•ᶜ 𝐸) = E′/E (⊖ 𝐸) ᵀΔ ν• E/E′ (⊖ 𝐸)
   ⊖₁ (νᵇᵇ_ {a = x •} {a} 𝐸) with (swap *ᵇ) (E/E′ (⊖ 𝐸)) | (swap *ᵇ) (E′/E (⊖ 𝐸))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a = νᵇ swap*E′/E ᵀΔ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {u •} 𝐸) with (swap *ᵇ) (E/E′ (⊖ 𝐸)) | (swap *ᵇ) (E′/E (⊖ 𝐸))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u = νᵇ swap*E′/E ᵀΔ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {• u} 𝐸) with (swap *ᵇ) (E/E′ (⊖ 𝐸)) | (swap *ᵇ) (E′/E (⊖ 𝐸))
   ... | swap*E/E′ | swap*E′/E = νᵇ swap*E′/E ᵀΔ νᵇ swap*E/E′
   ⊖₁ (νᵛᵛ_ {x = x} {u} 𝐸) with (swap *ᶜ) (E/E′ (⊖ 𝐸)) | (swap *ᶜ) (E′/E (⊖ 𝐸))
   ... | swap*E/E′ | swap*E′/E = νᶜ swap*E′/E ᵀΔ νᶜ swap*E/E′
   ⊖₁ (νᵇᶜ_ {a′ = a′} 𝐸) with (swap *ᶜ) (E′/E (⊖ 𝐸))
   ... | swap*E′/E rewrite swap∘push∘push a′ = νᶜ swap*E′/E ᵀΔ νᵇ E/E′ (⊖ 𝐸)
   ⊖₁ (νᶜᶜ 𝐸) = νᶜ (E′/E (⊖ 𝐸)) ᵀΔ νᶜ (E/E′ (⊖ 𝐸))
   ⊖₁ (! 𝐸) = E′/E (⊖ 𝐸) ᵀΔ E/E′ (⊖ 𝐸)

   ⊖ [ 𝐸 ] = ⊖₁ 𝐸
   ⊖ ([_]ˡ {a⌣a′ = ᵛ∇ᵛ} 𝐸) = E/E′ (⊖₁ 𝐸) ᵀΔ E′/E (⊖₁ 𝐸)
   ⊖ ([_]ˡ {a⌣a′ = ᵇ∇ᵇ} 𝐸) = E/E′ (⊖₁ 𝐸) ᵀΔ E′/E (⊖₁ 𝐸)
   ⊖ ([_]ˡ {a⌣a′ = ᵇ∇ᶜ} 𝐸) = E/E′ (⊖₁ 𝐸) ᵀΔ E′/E (⊖₁ 𝐸)
   ⊖ ([_]ˡ {a⌣a′ = ᶜ∇ᵇ} 𝐸) = E/E′ (⊖₁ 𝐸) ᵀΔ E′/E (⊖₁ 𝐸)
   ⊖ ([_]ˡ {a⌣a′ = ᶜ∇ᶜ} 𝐸) = E/E′ (⊖₁ 𝐸) ᵀΔ E′/E (⊖₁ 𝐸)
