module Transition.Concur.Cofinal where

   open import ProofRelevantPiCommon
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬγ; Action₂); open _ᴬ⌣_
   import Action.Ren
   open import Braiding.Proc using (_⋉̂_; module _⋉̂_; ⋉̂-sym; _⋉_; ⋉̂-to-⋉); open _⋉̂_
   open import Name as ᴺ using (Cxt; Name; toℕ; _+_; zero)
   open import Proc using (Proc); open Proc
   import Proc.Ren
   open import Ren as ᴿ using (Ren; suc; _ᴿ+_; pop; push; swap; +-preserves-id; +-preserves-involutivity);
      open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; tgt); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; Delta; module Delta′; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- related by a "bound" braid, by a "free" braid, or by identity. Parametric in the notion of bound braid.
   ⋈[_,_,_,_] : (∀ {Γ} → Proc Γ → Proc Γ → Set) → ∀ Γ {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) (Δ : Cxt) →
                let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in Proc (Γ′ + Δ) → Proc (Γ′ + Δ) → Set
   ⋈[ _ , Γ , ˣ∇ˣ , Δ ] P P′ = P ≡ P′
   ⋈[ _ , Γ , ᵇ∇ᵇ , Δ ] P P′ = ((swap ᴿ+ Δ) *) P ≡ P′ -- free braid
   ⋈[ _ , Γ , ᵇ∇ᶜ , Δ ] P P′ = P ≡ P′
   ⋈[ _ , Γ , ᶜ∇ᵇ , Δ ] P P′ = P ≡ P′
   ⋈[ _ , Γ , ᶜ∇ᶜ , Δ ] P P′ = P ≡ P′
   ⋈[ _⋉_ , Γ , ᵛ∇ᵛ , Δ ] P P′ = P ⋉ P′ -- bound braid

   -- Specialise cofinality to the irreflexive notion of bound braid.
   ⋈̂[_,_,_] : ∀ Γ {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) (Δ : Cxt) →
               let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in Proc (Γ′ + Δ) → Proc (Γ′ + Δ) → Set
   ⋈̂[ Γ , 𝑎 , Δ ] = ⋈[ _⋉̂_ , Γ , 𝑎 , Δ ]

   ⋈-sym : (_⋉̂_ : ∀ {Γ} → Proc Γ → Proc Γ → Set) → ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) (Δ : Cxt) →
           (∀ {Γ} → Symmetric (_⋉̂_ {Γ})) → Symmetric (⋈[ _⋉̂_ , Γ , 𝑎 , Δ ])
   ⋈-sym _⋉̂_ ˣ∇ˣ Δ ⋉̂-sym = sym
   ⋈-sym _⋉̂_ ᵇ∇ᵇ Δ ⋉̂-sym {i = P′} {j = P} P† =
      let open EqReasoning (setoid _) in
      begin
         ((swap ᴿ+ Δ) *) P
      ≡⟨ cong ((swap ᴿ+ Δ) *) (sym P†) ⟩
         ((swap ᴿ+ Δ) *) (((swap ᴿ+ Δ) *) P′)
      ≡⟨ involutive (+-preserves-involutivity swap Δ ᴿ.swap-involutive) P′ ⟩
         P′
      ∎
   ⋈-sym _⋉̂_ ᵇ∇ᶜ Δ ⋉̂-sym = sym
   ⋈-sym _⋉̂_ ᶜ∇ᵇ Δ ⋉̂-sym = sym
   ⋈-sym _⋉̂_ ᶜ∇ᶜ Δ ⋉̂-sym = sym
   ⋈-sym _⋉̂_ ᵛ∇ᵛ Δ ⋉̂-sym = ⋉̂-sym

   ⋈̂-sym : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) (Δ : Cxt) → Symmetric (⋈̂[ Γ , 𝑎 , Δ ])
   ⋈̂-sym 𝑎 Δ = ⋈-sym _⋉̂_ 𝑎 Δ ⋉̂-sym

   open Delta′

   γ₁ : ∀ {Γ} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {P R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) → ⋈̂[ Γ , 𝑎 , zero ] (tgt₁ (⊖₁ 𝐸)) (Proc↱ (sym (ᴬγ 𝑎)) (tgt₂(⊖₁ 𝐸)))
   γ₁ (E ᵇ│ᵇ F) = sym (cong₂ _│_ (swap∘push (tgt E)) (swap∘suc-push (tgt F)))
   γ₁ (E ᵇ│ᶜ F) = refl
   γ₁ (E ᶜ│ᵇ F) = refl
   γ₁ (E ᶜ│ᶜ F) = refl
   γ₁ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) = cong₂ _│_ (
      let open EqReasoning (setoid _); S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸) in
      begin
         (pop (push y) *) S
      ≡⟨ cong (pop (push y) *) (swap-swap (γ₁ 𝐸)) ⟩
         (pop (push y) *) ((swap *) S′)
      ≡⟨ sym (pop∘swap y _) ⟩
         (suc (pop y) *) S′
      ∎) refl
   γ₁ (_│•ᶜ_ {y = y} 𝐸 F) = cong₂ _│_ (cong (pop y *) (γ₁ 𝐸)) refl
   γ₁ (_ᵇ│•_ {y = y} E 𝐹) = cong₂ _│_ (sym (pop∘suc-push y _)) (γ₁ 𝐹)
   γ₁ (E ᶜ│• 𝐹) = cong₂ _│_ refl (γ₁ 𝐹)
   γ₁ (_│ᵥᵇ_ {a = a} 𝐸 F) with (id *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | id*E/E′ rewrite *-preserves-id ((push *) a) =
      let S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸)
          α : (id *) S ≡ (swap *) ((suc id *) S′)
          α = let open EqReasoning (setoid _) in
             begin
                (id *) S
             ≡⟨ *-preserves-id S ⟩
                S
             ≡⟨ swap-swap (γ₁ 𝐸) ⟩
                (swap *) S′
             ≡⟨ cong (swap *) (sym (+-id-elim 1 S′)) ⟩
                (swap *) ((suc id *) S′)
             ∎ in
      cong ν_ (cong₂ _│_ α (swap∘push _))
   γ₁ (_│ᵥᶜ_ {a = a} 𝐸 F) with (id *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | id*E/E′ rewrite *-preserves-id ((push *) a) =
      cong ν_ (cong₂ _│_ (cong (id *) (γ₁ 𝐸)) refl)
   γ₁ (_ᵇ│ᵥ_ {x = x} {𝑎 = ˣ∇ˣ} E 𝐹) = cong₂ _│_ (pop-zero∘suc-push (tgt E)) (γ₁ 𝐹)
   γ₁ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) = cong ν_ (cong₂ _│_ (swap∘push _) (swap-swap (γ₁ 𝐹)))
   γ₁ (E ᶜ│ᵥ 𝐹) = cong ν_ (cong₂ _│_ refl (γ₁ 𝐹))
   γ₁ (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} P 𝐹) = cong₂ _│_ refl (γ₁ 𝐹)
   γ₁ (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) = cong₂ _│_ (swap∘push∘push P) (γ₁ 𝐹)
   γ₁ (P │ᵇᶜ 𝐹) = cong₂ _│_ refl (γ₁ 𝐹)
   γ₁ (P │ᶜᶜ 𝐹) = cong₂ _│_ refl (γ₁ 𝐹)
   γ₁ (P │ᵛᵛ 𝐹) = refl │₂ (γ₁ 𝐹)
   γ₁ (_ᵇᵇ│_ {𝑎 = ˣ∇ˣ} 𝐸 _) = cong₂ _│_ (γ₁ 𝐸) refl
   γ₁ (_ᵇᵇ│_ {𝑎 = ᵇ∇ᵇ} 𝐸 Q) = cong₂ _│_ (γ₁ 𝐸) (swap∘push∘push Q)
   γ₁ (𝐸 ᵇᶜ│ Q) = cong₂ _│_ (γ₁ 𝐸) refl
   γ₁ (𝐸 ᶜᶜ│ Q) = cong₂ _│_ (γ₁ 𝐸) refl
   γ₁ (𝐸 ᵛᵛ│ Q) = (γ₁ 𝐸) │₁ refl
   γ₁ (𝐸 ➕₁ Q) = γ₁ 𝐸
   γ₁ (_│•_ {y = y} {z = z} 𝐸 𝐹) = cong₂ _│_ (
      let open EqReasoning (setoid _); S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸) in
      begin
         (pop z *) ((suc (pop y) *) S)
      ≡⟨ sym (pop-pop-swap y z _) ⟩
         (pop y *) ((suc (pop z) *) ((swap *) S))
      ≡⟨ cong (pop y *) (cong (suc (pop z) *) (γ₁ 𝐸)) ⟩
         (pop y *) ((suc (pop z) *) S′)
      ∎) (γ₁ 𝐹)
   γ₁ (_│•ᵥ_ {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ =
      let S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸)
          α : (suc (pop y) *) S ≡ (pop (ᴺ.suc y) *) S′
          α = let open EqReasoning (setoid _) in
             begin
                ((suc (pop y) *) S)
             ≡⟨ cong (suc (pop y) *) (sym (swap-involutive _ )) ⟩
                (suc (pop y) *) ((swap *) ((swap *) S))
             ≡⟨ cong (suc (pop y) *) (cong (swap *) (γ₁ 𝐸)) ⟩
                (suc (pop y) *) ((swap *) S′)
             ≡⟨ suc-pop∘swap y _ ⟩
                (pop (ᴺ.suc y) *) S′
             ∎ in
      cong ν_ (cong₂ _│_ α (γ₁ 𝐹))
   γ₁ (𝐸 │ᵥ 𝐹) =
      let S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸)
          α : (pop zero *) S ≡ (pop zero *) S′
          α = let open EqReasoning (setoid _) in
             begin
                (pop zero *) S
             ≡⟨ sym (pop-swap _) ⟩
                (pop zero *) ((swap *) S)
             ≡⟨ cong (pop zero *) (γ₁ 𝐸) ⟩
                (pop zero *) S′
             ∎ in
      cong ν_ (cong₂ _│_ α (γ₁ 𝐹))
   γ₁ (𝐸 │ᵥ′ 𝐹) rewrite sym (γ₁ 𝐸) | sym (γ₁ 𝐹) = νν-swapᵣ (tgt₁ (⊖₁ 𝐸) │ tgt₁ (⊖₁ 𝐹))
   γ₁ (ν• 𝐸) = γ₁ 𝐸
   γ₁ (ν•ᵇ 𝐸) = cong (swap *) (γ₁ 𝐸)
   γ₁ (ν•ᶜ 𝐸) = γ₁ 𝐸
   γ₁ (νᵇᵇ_ {a = x •} {a} 𝐸) with (swap *ᵇ) (E/E′ (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ | _ rewrite swap∘push∘push a =
      cong ν_ (
         let open EqReasoning (setoid _); S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸) in
         begin
            (suc swap *) ((swap *) ((suc swap *) S))
         ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
            (swap *) ((suc swap *) ((swap *) S))
         ≡⟨ cong (swap *) (cong (suc swap *) (γ₁ 𝐸)) ⟩
            (swap *) ((suc swap *) S′)
         ∎)
   γ₁ (νᵇᵇ_ {a = • x} {u •} 𝐸) = cong ν_ (
      let open EqReasoning (setoid _); S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸) in
      begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≡⟨ cong (swap *) (cong (suc swap *) (γ₁ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   γ₁ (νᵇᵇ_ {a = • x} {• u} 𝐸) = cong ν_ (
      let open EqReasoning (setoid _); S = tgt₁ (⊖₁ 𝐸); S′ = tgt₂(⊖₁ 𝐸) in
      begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≡⟨ cong (swap *) (cong (suc swap *) (γ₁ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   γ₁ (νˣˣ 𝐸) = cong ν_ (cong (swap *) (γ₁ 𝐸))
   γ₁ (νᵇᶜ_ {a′ = a′} 𝐸) with (swap *ᶜ) (E′/E (⊖₁ 𝐸))
   ... | _ rewrite swap∘push∘push a′ = cong ν_ (cong (swap *) (γ₁ 𝐸))
   γ₁ (νᶜᶜ 𝐸) = cong ν_ (γ₁ 𝐸)
   γ₁ (νᵛᵛ 𝐸) = ν (γ₁ 𝐸)
   γ₁ (! 𝐸) = γ₁ 𝐸

   -- Now symmetrise.
   γ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (𝐸 : E ⌣[ 𝑎 ] E′) → ⋈[ _⋉̂_ , Γ , 𝑎 , zero ] (tgt₁ (⊖ 𝐸)) (subst Proc (sym (ᴬγ 𝑎)) (tgt₂(⊖ 𝐸)))
   γ (inj₁ 𝐸) = γ₁ 𝐸
   γ (inj₂ 𝐸) with ⊖₁ 𝐸 | γ₁ 𝐸
   γ {𝑎 = ˣ∇ˣ} (inj₂ 𝐸) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   γ {𝑎 = ᵇ∇ᵇ} (inj₂ 𝐸) | E′/E ᵀΔ E/E′ | swap*S≡S′ =
      let open EqReasoning (setoid _); S = tgt E′/E; S′ = tgt E/E′ in
      begin
         (swap *) S′
      ≡⟨ cong (swap *) (sym swap*S≡S′) ⟩
         (swap *) ((swap *) S)
      ≡⟨ swap-involutive _ ⟩
         S
      ∎
   γ {𝑎 = ᵇ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   γ {𝑎 = ᶜ∇ᵇ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   γ {𝑎 = ᶜ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   γ {𝑎 = ᵛ∇ᵛ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≈S′ = ⋉̂-sym S≈S′

   γ-⋉ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (𝐸 : E ⌣[ 𝑎 ] E′) → ⋈[ _⋉_ , Γ , 𝑎 , zero ] (tgt₁ (⊖ 𝐸)) (subst Proc (sym (ᴬγ 𝑎)) (tgt₂(⊖ 𝐸)))
   γ-⋉ {𝑎 = ˣ∇ˣ} = γ
   γ-⋉ {𝑎 = ᵇ∇ᵇ} = γ
   γ-⋉ {𝑎 = ᵇ∇ᶜ} = γ
   γ-⋉ {𝑎 = ᶜ∇ᵇ} = γ
   γ-⋉ {𝑎 = ᶜ∇ᶜ} = γ
   γ-⋉ {𝑎 = ᵛ∇ᵛ} = ⋉̂-to-⋉ ∘ γ
