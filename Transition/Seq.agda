-- WIP: transition sequences and causal equivalence.
module Transition.Seq where

   open import SharedModules hiding (_⇒_; trans)
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren using (ren-preserves-inc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆; []; _ᵇ∷_)
   open import Action.Seq.Ren using (ren-preserves-inc⋆)
   open import Name as ᴺ using (Cxt; Name; _+_; +-assoc; zero; toℕ)
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≅_; ≅-sym; ≅-refl)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_; source; target)
   open import Transition.Concur using (_⌣_; module _Δ_; ⊖; coinitial; ᴬ⊖; ᴬ⊖-✓)
   open import Transition.Ren using (_Δ_; _*′)

   braid : ∀ {Γ} (n : Name 3) → Ren (Γ + toℕ n) (Γ + toℕ n)
   braid zero = id
   braid (ᴺ.suc zero) = id
   braid (ᴺ.suc (ᴺ.suc zero)) = swap
   braid (ᴺ.suc (ᴺ.suc (ᴺ.suc ())))

   ⋈[_,_,_] : ∀ Γ (n : Name 3) (m : Cxt) → Proc (Γ + toℕ n + m) → Proc (Γ + toℕ n + m) → Set
   ⋈[_,_,_] Γ n m P₁ P₂ = ((braid n ᴿ+ m) *) P₁ ≅ P₂

   -- TODO: consolidate.
   braid-preserves-inc : ∀ {Γ} (n : Name 3) m (a : Action (Γ + toℕ n + m)) →
                         Γ + toℕ n + m + inc (((braid n ᴿ+ m) *) a) ≡ Γ + toℕ n + (m + inc a)
   braid-preserves-inc n m a rewrite sym (ren-preserves-inc (braid n ᴿ+ m) a) = +-assoc _ m (inc a)

   braid-preserves-inc⋆ : ∀ {Γ} (n : Name 3) m (a⋆ : Action⋆ (Γ + toℕ n + m)) →
                         Γ + toℕ n + m + inc⋆ (((braid n ᴿ+ m) *) a⋆) ≡ Γ + toℕ n + (m + inc⋆ a⋆)
   braid-preserves-inc⋆ n m a⋆ rewrite sym (ren-preserves-inc⋆ (braid n ᴿ+ m) a⋆) = +-assoc _ m (inc⋆ a⋆)

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ n m a} {P P′ : Proc (Γ + toℕ n + m)} {R : Proc (Γ + toℕ n + m + inc a)}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc (Γ + toℕ n + (m + inc a))
         {R″} : Proc (Γ + toℕ n + m + inc (((braid n ᴿ+ m) *) a))
         γ/E : ⋈[ Γ , n , m + inc a ] (subst Proc (+-assoc _ m (inc a)) R) R′
         E/γ : P′ —[ ((braid n ᴿ+ m) *) a - ι ]→ R″

   ⊖′[_,_] : ∀ {ι Γ} n m {a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ′_ {n = n} {m = m} E γ
   ⊖′[ n , m ] {(_ •) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {(• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {• _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ

   ⊖′[_,_]-✓ : ∀ {ι Γ} n m {a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
               (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) → let _Δ_ {R′} {R″} _ _ = ⊖′[ n , m ] E γ in R′ ≅⁺ R″
   ⊖′[ n , m ]-✓ {(_ •) ᵇ} E γ = ≡-to-≅ refl
   ⊖′[_,_]-✓ n m {(• _) ᵇ} E γ = ≡-to-≅ refl
   ⊖′[_,_]-✓ n m {• _ 〈 _ 〉 ᶜ} E γ = ≡-to-≅ refl
   ⊖′[_,_]-✓ n m {τ ᶜ} E γ = ≡-to-≅ refl

   -- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
   -- composition is probably what we eventually want.
   infixr 5 _ᵇ∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _ᵇ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᵇ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᵇ∷ a⋆ ]→⋆ subst Proc (+-assoc _ _ (inc⋆ a⋆)) S

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ n m a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc (Γ + toℕ n + (m + inc⋆ a⋆))
         {R″} : Proc (Γ + toℕ n + m + inc⋆ (((braid n ᴿ+ m) *) a⋆))
         γ/E⋆ : ⋈[ Γ , n , m + inc⋆ a⋆ ] (subst Proc (+-assoc (Γ + toℕ n) m (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid n ᴿ+ m) *) a⋆ ]→⋆ R″

   ⊖⋆[_,_] : ∀ {Γ} n m {a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ⋆_ {n = n} {m = m} E⋆ γ
   ⊖⋆[ n , m ] [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} n m {a⋆ = • x ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ with ⊖′[ n , m ] E γ | ⊖′[ n , m ]-✓ E γ
   ... | _Δ_ {R′} {R″} γ/E E/γ | q with ⊖⋆[ n , m + 1 ] E⋆ γ/E
   ... | _Δ_ {S′} {S″} γ/E/E⋆ E⋆/γ/E =
      let b = ((braid n ᴿ+ m) *) (• x)
          b⋆ = ((braid n ᴿ+ m ᴿ+ 1) *) a⋆
          E/γ∷E⋆/γ/E : source E/γ —[ b ᵇ∷ b⋆ ]→⋆ subst Proc (+-assoc (Γ + toℕ n + m) 1 (inc⋆ b⋆)) S″
          E/γ∷E⋆/γ/E = E/γ ᵇ∷ {!E⋆/γ/E!}
      in {!!} Δ {!!}
{-
      let b = ((braid n ᴿ+ m) *) a
          b⋆ = ((braid n ᴿ+ m ᴿ+ 1) *) a⋆
          E/γ∷E⋆/γ/E : source E/γ —[ b ᵇ∷ b⋆ ]→⋆
                       subst Proc (+-assoc (Γ + toℕ n + m) 1 (inc⋆ b⋆))
                             (subst Proc (sym (braid-preserves-inc⋆ n (m + 1) a⋆)) S′)
          E/γ∷E⋆/γ/E = E/γ ᵇ∷ E⋆/γ/E
          goalᵣ : source E/γ —[ b ᵇ∷ b⋆ ]→⋆ subst Proc (sym (braid-preserves-inc⋆ n m (a ᵇ∷ a⋆))) _
          goalᵣ = {!!}
          goalₗ′ : ⋈[ Γ , n , m + 1 + inc⋆ a⋆ ] (subst Proc (+-assoc (Γ + toℕ n) (m + 1) (inc⋆ a⋆)) _) S′
          goalₗ′ = γ/E/E⋆
          goalₗ : ⋈[ Γ , n , m + (1 + inc⋆ a⋆) ] (subst Proc (+-assoc (Γ + toℕ n) m (1 + inc⋆ a⋆))
                                                       (subst Proc (+-assoc (Γ + toℕ n + m) 1 (inc⋆ a⋆))
                                                              _)) {!!}
          goalₗ = {!!}
      in goalₗ Δ goalᵣ
-}
   ⊖⋆[_,_] {Γ} n m {a⋆ = x • ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ = {!!}
{-
   -- Causal equivalence. TODO: fix [_∶⇋∶_]∷_ rule; needs more general notion of cofinality.
   infix 4 _≃_
   infixr 9 _≃-∘_
   data _≃_ {Γ} {P : Proc Γ} : ∀ {a⋆ R a′⋆ R′} → P —[ a⋆ ]→⋆ R → P —[ a′⋆ ]→⋆ R′ → Set where
      --- Transposition rule.
      [_∶⇋∶_]∷_ : ∀ {a R a′ R′} (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) →
                  ⦃ E⌣E′ : E ⌣ E′ ⦄ → E ⌣ E′ → let open _Δ_ (⊖ E⌣E′); Q = target E′/E in
                  ∀ {a⋆ S a′⋆ S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                  E ∷ E′/E ∷ E⋆ ≃ E′ ∷ E/E′ ∷ []
      -- Close under trace constructors.
      [] : [] ≃ []
      _∷_ : ∀ {a R a⋆ S a′⋆ S′} (E : P —[ a - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
            E⋆ ≃ E′⋆ → E ∷ E⋆ ≃ E ∷ E′⋆
      -- Transitivity and symmetry.
      _≃-∘_ : ∀ {a⋆ R a″⋆ S a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {F⋆ : P —[ a″⋆ ]→⋆ S} {E′⋆ : P —[ a′⋆ ]→⋆ R′} →
            F⋆ ≃ E′⋆ → E⋆ ≃ F⋆ → E⋆ ≃ E′⋆
      ≃-sym : ∀ {a⋆ R a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {E′⋆ : P —[ a′⋆ ]→⋆ R′} → E⋆ ≃ E′⋆ → E′⋆ ≃ E⋆

   -- TODO: IsEquivalence instance.
-}
