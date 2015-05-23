module Transition.Concur2 where

   open import SharedModules hiding ([_])

   open import Ext

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc; coinitial; coinitial-sym);
      open ᴬ.Actionᵇ; open ᴬ.Actionᶜ; open ᴬ.coinitial
   open import Action.Ren using (_*†)
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; ᴺren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   ᴬΔ : ∀ {Γ} {a a′ : Action Γ} → coinitial a a′ → Set
   ᴬΔ {Γ} ᵛ∇ᵛ = Actionᶜ (Γ + 1)
   ᴬΔ {Γ} ᵇ∇ᵇ = Actionᵇ (Γ + 1)
   ᴬΔ {Γ} ᵇ∇ᶜ = Actionᶜ (Γ + 1)
   ᴬΔ {Γ} ᶜ∇ᵇ = Actionᵇ Γ
   ᴬΔ {Γ} ᶜ∇ᶜ = Actionᶜ Γ

   -- The residual a′/a. Note that ᵇ∇ᵇ may also relate two bound outputs, but only if they represent
   -- extrusions of distinct binders.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : coinitial a a′) → ᴬΔ a⌣a′
   ᴬ⊖ (ᵛ∇ᵛ {u = u}) = • ᴺ.suc u 〈 zero 〉
   ᴬ⊖ (ᵇ∇ᵇ {a′ = a′}) = (push *) a′
   ᴬ⊖ (ᵇ∇ᶜ {a′ = a′}) = (push *) a′
   ᴬ⊖ (ᶜ∇ᵇ {a′ = a′}) = a′
   ᴬ⊖ (ᶜ∇ᶜ {a′ = a′}) = a′

   -- Whether two coinitial evaluation contexts are concurrent. Only give the left rules, then symmetrise.
   -- Convenient to have this indexed by the kind of action residual. TODO: cases for •│ and ᵥ│.
   syntax Concur₁ E E′ a′/a = E ⌣₁[ a′/a ] E′
   infix 4 Concur₁

   data Concur₁ {Γ} : ∀ {a : Action Γ} {a′ : Action Γ} {P R R′} →
                P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → coinitial a a′ → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᵇ ] P │ᵇ F
      _ᵇ│ᶜ_ : ∀ {P Q R S} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F
      _ᶜ│ᵇ_ : ∀ {P Q R S} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᵇ ] P │ᵇ F
      _ᶜ│ᶜ_ : ∀ {P Q R S} {a a′ : Actionᶜ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F
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
      _ᵇ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │ᵥ F′
      _ᶜ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᶜ∇ᵇ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │ᵥ F′
      _➕₁_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
             E ⌣₁[ a⌣a′ ] E′ → (Q : Proc Γ) → E ➕₁ Q ⌣₁[ a⌣a′ ] E′ ➕₁ Q
      _│ᵇᵇ_ : ∀ {Q S S′} {a a′ : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᵇ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ a⌣a′ ] P │ᵇ F′
      _│ᵇᶜ_ : ∀ {Q S S′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F′
      _│ᶜᶜ_ : ∀ {Q S S′} {a a′ : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F′
      _ᵇᵇ│_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a⌣a′} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′} →
              E ⌣₁[ a⌣a′ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ a⌣a′ ] E′ ᵇ│ Q
      _ᵇᶜ│_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᵇ∇ᶜ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ ᶜ│ Q
      _ᶜᶜ│_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᶜ ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ ᶜ│ Q
      _│•_ : ∀ {x y u z P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ • u 〈 z 〉 ᶜ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᶜ∇ᶜ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │• F′
      _│ᵥ_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {•x⌣•u} {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ •x⌣•u ] F′ → E │ᵥ F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      ν•_ : ∀ {x u P R R′} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ • ᴺ.suc u 〈 zero 〉 ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵛ∇ᵛ ] ν• E′
      ν•ᵇ_ : ∀ {x P R R′} {a : Actionᵇ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᵇ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᵇ ] E′ → ν• E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      ν•ᶜ_ : ∀ {x P R R′} {a : Actionᶜ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᵇᵇ_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a⌣a′} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᵇ - _ ]→ R′} →
          E ⌣₁[ (push *†) a⌣a′ ] E′ → νᵇ E ⌣₁[ a⌣a′ ] νᵇ E′
      νᵇᶜ_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁[ {!!} ] E′ → νᵇ E ⌣₁[ {!!} ] νᶜ E′
      νᶜᶜ_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ (push *) a ᶜ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁[ {!!} ] E′ → νᶜ E ⌣₁[ {!!} ] νᶜ E′
      !_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P │ ! P —[ a - _ ]→ R} {E′ : P │ ! P —[ a′ - _ ]→ R′} →
           E ⌣₁[ a⌣a′ ] E′ → ! E ⌣₁[ a⌣a′ ] ! E′

   syntax Concur E E′ a′/a = E ⌣[ a′/a ] E′

   Concur : ∀ {Γ} {a : Action Γ} {a′ : Action Γ} {P R R′}
            (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → coinitial a a′ → Set
   Concur E E′ a′/a = E ⌣₁[ a′/a ] E′ ⊎ E′ ⌣₁[ coinitial-sym a′/a ] E
