-- WIP: transition sequences and causal equivalence.
module Transition.Seq where

   open import SharedModules hiding (_⇒_)
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.HeterogeneousEquality

   open import Ext

   open import Action as ᴬ using (Action; _ᵇ; _ᶜ; inc)
   open import Action.Ren using (ren-preserves-inc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆; []; _ᵇ∷_; _ᶜ∷_)
   open import Action.Seq.Ren using (ren-preserves-inc⋆)
   open import Name as ᴺ using (Cxt; Name; _+_; +-assoc; zero; toℕ; +-left-identity)
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≅_; ≅-sym; ≅-refl)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_; source; target)
   open import Transition.Concur using (_⌣_; module _Δ_; ⊖; coinitial; ᴬ⊖; ᴬ⊖-✓)
   open import Transition.Ren using (_Δ_; _*′)

   Proc∼ = subst Proc
   Proc≅ = ≡-subst-removable Proc

   braid : ∀ {Γ} (n : Name 3) → Ren (Γ + toℕ n) (Γ + toℕ n)
   braid zero = id
   braid (ᴺ.suc zero) = id
   braid (ᴺ.suc (ᴺ.suc zero)) = swap
   braid (ᴺ.suc (ᴺ.suc (ᴺ.suc ())))

   ⋈[_,_,_] : ∀ Γ (n : Name 3) (m : Cxt) → Proc (Γ + toℕ n + m) → Proc (Γ + toℕ n + m) → Set
   ⋈[ Γ , n , m ] P P′ = ((braid n ᴿ+ m) *) P ≅ P′

   quibble : ∀ Γ (ρ : Ren Γ Γ) Δ† Δ′ Δ″ (S : Proc (Γ + Δ† + Δ′ + Δ″)) (S′ : Proc (Γ + (Δ† + Δ′ + Δ″))) →
             ((ρ ᴿ+ (Δ† + Δ′ + Δ″))*)
             (Proc∼ (+-assoc Γ (Δ† + Δ′) Δ″) (Proc∼ (cong (flip _+_ Δ″) (+-assoc Γ Δ† Δ′)) S)) ≅ S′ →
             ((ρ ᴿ+ (Δ† + (Δ′ + Δ″)))*)
             (Proc∼ (+-assoc Γ Δ† (Δ′ + Δ″))
                    (Proc∼ (+-assoc (Γ + Δ†) Δ′ Δ″) S)) ≅ Proc∼ (cong (_+_ Γ) (+-assoc Δ† Δ′ Δ″)) S′
   quibble = {!!}

   ren-preserves-inc-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ m (a : Action (Γ + m)) →
                             Γ + (m + inc a) ≡ Γ + m + inc (((ρ ᴿ+ m) *) a)
   ren-preserves-inc-assoc {Γ} ρ m a =
      trans (sym (+-assoc Γ m (inc a))) (cong (_+_ (Γ + m)) (ren-preserves-inc (ρ ᴿ+ m) a))

   ren-preserves-inc⋆-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) → ∀ m (a⋆ : Action⋆ (Γ + m)) →
                              Γ + (m + inc⋆ a⋆) ≡ Γ + m + inc⋆ (((ρ ᴿ+ m) *) a⋆)
   ren-preserves-inc⋆-assoc {Γ} ρ m a⋆ =
      trans (sym (+-assoc Γ m (inc⋆ a⋆))) (cong (_+_ (Γ + m)) (ren-preserves-inc⋆ (ρ ᴿ+ m) a⋆))

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ n m a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E : ⋈[ Γ , n , m + inc a ] (Proc∼ (+-assoc _ m (inc a)) R) R′
      σ = braid {Γ} n
      field
         E/γ : P′ —[ ((σ ᴿ+ m) *) a - ι ]→ Proc∼ (ren-preserves-inc-assoc σ m a) R′

   ⊖′[_,_] : ∀ {ι Γ} n m {a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
         (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ′_ {n = n} {m = m} E γ
   ⊖′[ n , m ] {(_ ᴬ.•) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {(ᴬ.• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.• _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ

   -- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
   -- composition is probably what we eventually want.
   infixr 5 _ᵇ∷_ _ᶜ∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _ᵇ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᵇ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᵇ∷ a⋆ ]→⋆ Proc∼ (+-assoc _ _ (inc⋆ a⋆)) S
      _ᶜ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᶜ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᶜ∷ a⋆ ]→⋆ Proc∼ (+-assoc _ _ (inc⋆ a⋆)) S

   target⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   target⋆ {R = R} _ = R

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. Cofinal by construction.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ n m a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E⋆ : ⋈[ Γ , n , m + inc⋆ a⋆ ] (Proc∼ (+-assoc _ _ (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid n ᴿ+ m) *) a⋆ ]→⋆ Proc∼ (ren-preserves-inc⋆-assoc (braid n) m a⋆) R′

   ⊖⋆[_,_] : ∀ {Γ} n m {a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ⋆_ {n = n} {m = m} E⋆ γ
   ⊖⋆[ n , m ] [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} n m {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ with ⊖′[ n , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ n , m + 1 ] E⋆ γ/E | ren-preserves-inc-assoc (braid n) m (a ᵇ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl =
      let Γ′ = Γ + toℕ n
          σ = braid {Γ} n
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᵇ∷ ((σ ᴿ+ m ᴿ+ 1) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc∼ (+-assoc (Γ′ + m) 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆)))
                         (Proc∼ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′)
                ≅⟨ Proc≅ (+-assoc (Γ′ + m) 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆))) _ ⟩
                   Proc∼ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′
                ≅⟨ Proc≅ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′ ⟩
                   S′
                ≅⟨ ≅⁺-sym (Proc≅ (cong (_+_ Γ′) (+-assoc m 1 (inc⋆ a⋆))) S′) ⟩
                   Proc∼ (cong (_+_ Γ′) (+-assoc m 1 (inc⋆ a⋆))) S′
                ≅⟨ ≅⁺-sym (Proc≅ (ren-preserves-inc⋆-assoc σ m (a ᵇ∷ a⋆)) _) ⟩
                   Proc∼ (ren-preserves-inc⋆-assoc σ m (a ᵇ∷ a⋆))
                         (Proc∼ (cong (_+_ Γ′) (+-assoc m 1 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᵇ∷ E⋆/γ/E)
      in quibble _ σ m 1 (inc⋆ a⋆) (target⋆ E⋆) S′ γ/E/E⋆ Δ E/γ∷E⋆/γ/E
   ⊖⋆[_,_] {Γ} n m {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) γ with ⊖′[ n , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ n , m ] E⋆ γ/E | ren-preserves-inc-assoc (braid n) m (a ᶜ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl =
      let Γ′ = Γ + toℕ n
          σ = braid {Γ} n
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᶜ∷ ((σ ᴿ+ m) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc∼ (+-assoc (Γ′ + m) 0 (inc⋆ (((σ ᴿ+ m) *) a⋆)))
                         (Proc∼ (ren-preserves-inc⋆-assoc σ m a⋆) S′)
                ≅⟨ Proc≅ (+-assoc (Γ′ + m) 0 (inc⋆ (((σ ᴿ+ m) *) a⋆))) _ ⟩
                   Proc∼ (ren-preserves-inc⋆-assoc σ m a⋆) S′
                ≅⟨ Proc≅ (ren-preserves-inc⋆-assoc σ m a⋆) S′ ⟩
                   S′
                ≅⟨ ≅⁺-sym (Proc≅ (cong (_+_ Γ′) (+-assoc m 0 (inc⋆ a⋆))) S′) ⟩
                   Proc∼ (cong (_+_ Γ′) (+-assoc m 0 (inc⋆ a⋆))) S′
                ≅⟨ ≅⁺-sym (Proc≅ (ren-preserves-inc⋆-assoc σ m (a ᶜ∷ a⋆)) _) ⟩
                   Proc∼ (ren-preserves-inc⋆-assoc σ m (a ᶜ∷ a⋆))
                         (Proc∼ (cong (_+_ Γ′) (+-assoc m 0 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᶜ∷ E⋆/γ/E)
      in quibble _ σ m 0 (inc⋆ a⋆) (target⋆ E⋆) S′ γ/E/E⋆ Δ E/γ∷E⋆/γ/E
{-
   -- Causal equivalence. TODO: fix [_∶⇋∶_]∷_ rule; needs more general notion of cofinality.
   infix 4 _≃_
   infixr 9 _≃-∘_
   data _≃_ {Γ} {P : Proc Γ} : ∀ {a⋆ R a′⋆ R′} → P —[ a⋆ ]→⋆ R → P —[ a′⋆ ]→⋆ R′ → Set where
      --- Transposition rule.
      [_ᵇ∶⇋∶ᵇ_]∷_ : ∀ {a R a′ R′} (E : P —[ a ᵇ - _ ]→ R) (E′ : P —[ a′ ᵇ - _ ]→ R′) →
                  ⦃ E⌣E′ : E ⌣ E′ ⦄ → E ⌣ E′ → let open _Δ_ (⊖ E⌣E′); Q = target E′/E in
                  ∀ {a⋆ S a′⋆ S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                  E ᵇ∷ E′/E ᵇ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᵇ∷ []
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
