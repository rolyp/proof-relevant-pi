-- The residual of a concurrent pair after a transition (residuation preserves concurrency).
-- There is an unpleasant case-explosion here because of the need to distinguish the ᵛ∇ᵛ and ᵇ∇ᵇ cases pairwise
-- across the three transitions.
--
-- Agda is unable to compile this file. It requires a larger stack (I used +RTS -K40M -RTS), but even then it
-- runs out of heap on my machine.
module Transition.Concur.Transition where

   open import SharedModules
   open import Ext

   open import Action as ᴬ using (Action; _ᴬ⌣_; ᴬ⌣-sym); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ; open ᴬ._ᴬ⌣_
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   open import Ren as ᴿ using (Ren; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
   open import Transition.Concur2
      using (
         Concur; Concur₁; module Concur; module Concur₁; Delta′; module Delta′; Delta; ⊖; ⊖₁; ⌣-sym
      );
      open Concur; open Concur₁; open Delta′
   open import Transition.Concur.Ren2 using (/-preserves-ᴬ⌣; _*ᵇᵇ⌣; _*ᵇᶜ⌣; _*ᶜᵇ⌣; _*ᶜᶜ⌣)

   -- These are trivial to prove; one just pattern-matches the a⌣a′ component of 𝐸 and 𝐸″ so that Agda can
   -- see that /-preserves-⌣ has the type required, and then use that. However, just postulate these so
   -- they don't become a factor in memory usage.
   postulate
      /-preserves-⌣ᴰᴰᵁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a″⌣a : a″ ᴬ⌣ a}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                        (𝐸 : E ⌣[ a⌣a′ ] E′) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                        E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ (ᴬ⌣-sym a″⌣a) ] E/E′ (⊖ 𝐸″)
      /-preserves-⌣ᴰᵁᴰ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a″⌣a′ : a″ ᴬ⌣ a′} {a⌣a″ : a ᴬ⌣ a″}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                        (𝐸 : E ⌣[ a⌣a′ ] E′) → E″ ⌣[ a″⌣a′ ] E′ → (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                        E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ a⌣a′ (ᴬ⌣-sym a″⌣a′) a⌣a″ ] E′/E (⊖ 𝐸″)
      /-preserves-⌣ᴰᵁᵁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a″⌣a′ : a″ ᴬ⌣ a′} {a″⌣a : a″ ᴬ⌣ a}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                        (𝐸 : E ⌣[ a⌣a′ ] E′) → E″ ⌣[ a″⌣a′ ] E′ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                        E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ a⌣a′ (ᴬ⌣-sym a″⌣a′) (ᴬ⌣-sym a″⌣a) ] E/E′ (⊖ 𝐸″)
      /-preserves-⌣ᵁᴰᴰ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a : a′ ᴬ⌣ a} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                        (𝐸 : E′ ⌣[ a′⌣a ] E) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                        E/E′ (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a) a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
      /-preserves-⌣ᵁᴰᵁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a : a′ ᴬ⌣ a} {a′⌣a″ : a′ ᴬ⌣ a″} {a″⌣a : a″ ᴬ⌣ a}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                        (𝐸 : E′ ⌣[ a′⌣a ] E) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                        E/E′ (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a) a′⌣a″ (ᴬ⌣-sym a″⌣a) ] E/E′ (⊖ 𝐸″)
      /-preserves-⌣ᵁᵁᴰ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a : a′ ᴬ⌣ a} {a″⌣a′ : a″ ᴬ⌣ a′} {a⌣a″ : a ᴬ⌣ a″}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                        (𝐸 : E′ ⌣[ a′⌣a ] E) → E″ ⌣[ a″⌣a′ ] E′ → (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                        E/E′ (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a) (ᴬ⌣-sym a″⌣a′) a⌣a″ ] E′/E (⊖ 𝐸″)
      /-preserves-⌣ᵁᵁᵁ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a : a′ ᴬ⌣ a} {a″⌣a′ : a″ ᴬ⌣ a′} {a″⌣a : a″ ᴬ⌣ a}
                        {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                        (𝐸 : E′ ⌣[ a′⌣a ] E) → E″ ⌣[ a″⌣a′ ] E′ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                        E/E′ (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a) (ᴬ⌣-sym a″⌣a′) (ᴬ⌣-sym a″⌣a) ] E/E′ (⊖ 𝐸″)

   /-preserves-⌣ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                   {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                   (𝐸 : E ⌣[ a⌣a′ ] E′) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                   E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)

{-
   │ᵥ•-preserves : ∀ {Γ} {P Q : Proc Γ} {x u y a″ R R′ R″ S S′} {a′⌣a″} {a⌣a″}
                   {E : P —[ (x •) ᵇ - _ ]→ R} {F : Q —[ (• x) ᵇ - _ ]→ S}
                   {E′ : P —[ (u •) ᵇ - _ ]→ R′} {F′ : Q —[ • u 〈 y 〉 ᶜ - _ ]→ S′} {E″ : P │ Q —[ a″ - _ ]→ R″}
                   (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣[ ᵇ∇ᶜ ] F′) → E′ │• F′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E │ᵥ F ⌣[ a⌣a″ ] E″) →
                   E′/E (⊖ [ 𝐸 │ᵥ• 𝐹 ]) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)

   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │• 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] = [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │• 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 (⌣-sym 𝐸′) 𝐸″ │• /-preserves-⌣ 𝐹 (⌣-sym 𝐹′) 𝐹″ ] ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │•ᵇ F ]ˡ [ 𝐸″ │ᵥᵇ F′ ]ˡ = [ νᵇᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │•ᵇ _ ] ]ˡ
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │•ᶜ F ]ˡ [ 𝐸″ │ᵥᶜ F′ ]ˡ = [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │•ᶜ _ ]ˡ ]
   │ᵥ•-preserves 𝐸 𝐹 [ E′ ᵇ│• 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹″ ]ˡ = [ νᵇᶜ [ _ ᵇ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ] ]ˡ
   │ᵥ•-preserves 𝐸 𝐹 [ E′ ᵇ│• 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ = [ ν•ᶜ [ _ ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ] ]ˡ
   │ᵥ•-preserves 𝐸 𝐹 [ E′ ᶜ│• 𝐹′ ]ˡ [ E ᶜ│ᵥ 𝐹″ ]ˡ = [ νᶜᶜ [ _ ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ•-preserves 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ•-preserves _ _ [ _ │• _ ] [ () ]ˡ
   │ᵥ•-preserves _ _ [ _ │•ᵇ _ ]ˡ [ () ]
   │ᵥ•-preserves _ _ [ _ │•ᶜ _ ]ˡ [ () ]
   │ᵥ•-preserves _ _ [ _ ᵇ│• _ ]ˡ [ () ]
   │ᵥ•-preserves _ _ [ _ ᶜ│• _ ]ˡ [ () ]
   │ᵥ•-preserves _ _ [ _ │• _ ]ˡ [ () ]ˡ

   │ᵥ•ˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {x u y a″ R R′ R″ S S′} {a′⌣a″} {a⌣a″}
                   {E : P —[ (x •) ᵇ - _ ]→ R} {F : Q —[ (• x) ᵇ - _ ]→ S}
                   {E′ : P —[ (u •) ᵇ - _ ]→ R′} {F′ : Q —[ • u 〈 y 〉 ᶜ - _ ]→ S′} {E″ : P │ Q —[ a″ - _ ]→ R″}
                   (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣[ ᵇ∇ᶜ ] F′) → E │ᵥ F ⌣[ a′⌣a″ ] E″ → (𝐸″ : E′ │• F′ ⌣[ a⌣a″ ] E″) →
                   E′/E (⊖ [ 𝐸 │ᵥ• 𝐹 ]ˡ) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ] [ 𝐸″ │• 𝐹″ ] =
      [ (pop y *ᵇᵇ⌣) (⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸″ 𝐸′ 𝐸)) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹″ 𝐹′ 𝐹) ]
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ 𝐸′ │ᵥ• 𝐹′ ] [ 𝐸″ │• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″) │ᵥ• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ 𝐸′ │ᵥ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ _│ᵥᵇ_ {a = a} 𝐸′ F ]ˡ [ 𝐸″ │•ᵇ F′ ]ˡ
      with (pop y *ᵇ) (E/E′ (⊖ 𝐸)) | (pop y *ᵇ) (E/E′ (⊖ 𝐸″)) | (pop y *ᵇᵇ⌣) (⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″))
   ... | _ | _ | pop-y*𝐸′/E′ rewrite pop∘push y a = [ pop-y*𝐸′/E′ │ᵥᵇ _ ]ˡ
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ _│ᵥᶜ_ {a = a} 𝐸′ F ]ˡ [ 𝐸″ │•ᶜ F′ ]ˡ
      with (pop y *ᵇ) (E/E′ (⊖ 𝐸)) | (pop y *ᶜ) (E/E′ (⊖ 𝐸″)) | (pop y *ᶜᵇ⌣) (⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″))
   ... | _ | _ | pop-y*𝐸′/E′ rewrite pop∘push y a = [ pop-y*𝐸′/E′ │ᵥᶜ _ ]ˡ
   │ᵥ•ˡ-preserves {x = x} {y = y} 𝐸 𝐹 [ E ᵇ│ᵥ 𝐹′ ]ˡ [ E′ ᵇ│• 𝐹″ ]ˡ with (pop y *ᵇ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y (x •) = [ pop-y*E/E′ ᵇ│ᵥ ⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   │ᵥ•ˡ-preserves 𝐸 𝐹 [ E ᶜ│ᵥ 𝐹′ ]ˡ [ E′ ᶜ│• 𝐹″ ]ˡ = [ _ ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᵥ•ˡ-preserves {y = y} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᵥ•ˡ-preserves _ _ [ _ │ᵥ _ ] [ () ]
   │ᵥ•ˡ-preserves _ _ [ _ │ᵥᵇ _ ]ˡ [ () ]
   │ᵥ•ˡ-preserves _ _ [ _ │ᵥᶜ _ ]ˡ [ () ]
   │ᵥ•ˡ-preserves _ _ [ _ ᵇ│ᵥ _ ]ˡ [ () ]
   │ᵥ•ˡ-preserves _ _ [ _ ᶜ│ᵥ _ ]ˡ [ () ]
   │ᵥ•ˡ-preserves _ _ [ _ │ᵥ _ ]ˡ [ () ]

   │ᵥᵇ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a″ x R R′ R″ S} {a′⌣a″ : τ ᶜ ᴬ⌣ a″} {a⌣a″ : a ᵇ ᴬ⌣ a″}
                  {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ (x •) ᵇ - _ ]→ R′} (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′)
                  (F : Q —[ (• x) ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″}
                  (𝐸′ : E′ │ᵥ F ⌣[ a′⌣a″ ] E″) (𝐸″ : E ᵇ│ Q ⌣[ a⌣a″ ] E″) →
                  E′/E (⊖ 𝐸) │ᵥ (push *ᵇ) F ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥᵇ-preserves {a = a} 𝐸 F [ _│ᵥ•_ {y = y} 𝐸′ 𝐹′ ] [ 𝐸″ │•ᵇ F′ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• (push *ᵇᶜ⌣) 𝐹′ ]
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥ 𝐹′ ] [ 𝐸″ │ᵥᵇ F′ ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ (push *ᵇᵇ⌣) 𝐹′ ]
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ Q ] =
      [ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″) │ᵥᵇ (push *ᵇ) F ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ Q ] =
      [ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″) │ᵥᶜ (push *ᵇ) F ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ .F ]ˡ [ 𝐸″ ᵇᶜ│ Q ] = [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 │ᵥᶜ (push *ᵇ) F ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ E ᵇ│ᵥ 𝐹′ ]ˡ [ E′ ᵇ│ᵇ F′ ] = [ E′/E (⊖ 𝐸) ᵇ│ᵥ (push *ᵇᵇ⌣) 𝐹′ ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ E ᶜ│ᵥ 𝐹′ ]ˡ [ E′ ᵇ│ᶜ F′ ] = [ E′/E (⊖ 𝐸) ᶜ│ᵥ (push *ᶜᵇ⌣) 𝐹′ ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥ 𝐹′ ]ˡ [ 𝐸″ │ᵥᵇ F′ ] = [ ⌣-sym (/-preserves-⌣ 𝐸″ 𝐸′ 𝐸) │ᵥ ⌣-sym ((push *ᵇᵇ⌣) 𝐹′) ]
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ Q ]ˡ = [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥᵇ (push *ᵇ) F ]ˡ
   │ᵥᵇ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ Q ]ˡ = [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥᶜ (push *ᵇ) F ]ˡ
   │ᵥᵇ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   │ᵥᵇ-preserves _ _ [ _ │ᵥ _ ] [ () ]ˡ
   │ᵥᵇ-preserves _ _ [ _ │ᵥᶜ ._ ]ˡ [ () ]ˡ
   │ᵥᵇ-preserves _ _ [ _ ᵇ│ᵥ _ ]ˡ [ () ]ˡ
   │ᵥᵇ-preserves _ _ [ _ ᶜ│ᵥ _ ]ˡ [ () ]ˡ
   │ᵥᵇ-preserves _ _ [ _ │ᵥ _ ]ˡ [ () ]ˡ

   │ᵥᵇˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a″ x R R′ R″ S} {a′⌣a″ : a ᵇ ᴬ⌣ a″} {a⌣a″ : τ ᶜ ᴬ⌣ a″}
                  {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ (x •) ᵇ - _ ]→ R′} (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′)
                  (F : Q —[ (• x) ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″}
                  (𝐸′ : E ᵇ│ Q ⌣[ a′⌣a″ ] E″) (𝐸″ : E′ │ᵥ F ⌣[ a⌣a″ ] E″) →
                  νᵇ (E/E′ (⊖ 𝐸) ᵇ│ S) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ │•ᵇ F′ ] [ 𝐸″ │ᵥ• 𝐹 ] = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᵇ E′/E (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ F′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹 ] = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥᵇ E′/E (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ F′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹 ] = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᵇ E′/E (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ E ᵇ│ᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹 ]ˡ = [ νᵇᵇ [ E/E′ (⊖ 𝐸) ᵇ│ᵇ E/E′ (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ E ᵇ│ᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹 ]ˡ = [ ν•ᵇ [ E/E′ (⊖ 𝐸) ᵇ│ᶜ E/E′ (⊖ 𝐹) ]ˡ ]ˡ
   │ᵥᵇˡ-preserves 𝐸 F [ E ᵇ│ᶜ F′ ] [ E′ ᶜ│ᵥ 𝐹 ]ˡ = [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│ᶜ E/E′ (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ F′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹 ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥᵇ E/E′ (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ F′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹 ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │•ᵇ E/E′ (⊖ 𝐹) ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸′ Q ] [ 𝐸″ │ᵥᵇ .F ]ˡ = [ νᵇᵇ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ _ ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸′ Q ] [ 𝐸″ │ᵥᵇ .F ]ˡ = [ νᵛᵛ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ _ ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ 𝐸′ ᵇᶜ│ Q ] [ 𝐸″ │ᵥᶜ .F ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ _ ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸′ Q ]ˡ [ 𝐸″ │ᵥᵇ .F ]ˡ = [ νᵇᵇ [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ _ ] ]
   │ᵥᵇˡ-preserves 𝐸 F [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸′ Q ]ˡ [ 𝐸″ │ᵥᵇ .F ]ˡ = [ νᵛᵛ [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ _ ] ]
   │ᵥᵇˡ-preserves _ _ [ _ ᵇ│ᵇ _ ] [ () ]
   │ᵥᵇˡ-preserves _ _ [ _ ᵇ│ᶜ _ ] [ () ]
   │ᵥᵇˡ-preserves _ _ [ _ ᵇᵇ│ _ ] [ () ]
   │ᵥᵇˡ-preserves _ _ [ _ ᵇᶜ│ _ ] [ () ]
   │ᵥᵇˡ-preserves _ _ [ _ │•ᵇ _ ] [ () ]ˡ
   │ᵥᵇˡ-preserves _ _ [ _ ᵇᵇ│ _ ]ˡ [ () ]

   │ᵥᶜ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a″ x R R′ R″ S} {a′⌣a″ : τ ᶜ ᴬ⌣ a″} {a⌣a″ : a ᶜ ᴬ⌣ a″}
                  {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ (x •) ᵇ - _ ]→ R′} (𝐸 : E ⌣[ ᶜ∇ᵇ ] E′)
                  (F : Q —[ (• x) ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″}
                  (𝐸′ : E′ │ᵥ F ⌣[ a′⌣a″ ] E″) (𝐸″ : E ᶜ│ Q ⌣[ a⌣a″ ] E″) →
                  E′/E (⊖ 𝐸) │ᵥ F ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥᶜ-preserves 𝐸 F [ _│ᵥ•_ {y = y} 𝐸′ 𝐹 ] [ _│•ᶜ_ {a = a} 𝐸″ F′ ] with (pop y *ᶜ) (E/E′ (⊖ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• 𝐹 ]
   │ᵥᶜ-preserves 𝐸 F [ 𝐸′ │ᵥ 𝐹 ] [ 𝐸″ │ᵥᶜ F′ ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ 𝐹 ]
   │ᵥᶜ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ .F ]ˡ [ 𝐸″ ᶜᶜ│ Q ] = [ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″) │ᵥᶜ F ]ˡ
   │ᵥᶜ-preserves 𝐸 F [ E′ ᵇ│ᵥ 𝐹 ]ˡ [ E ᶜ│ᵇ F′ ] = [ E′/E (⊖ 𝐸) ᵇ│ᵥ 𝐹 ]ˡ
   │ᵥᶜ-preserves 𝐸 F [ E′ ᶜ│ᵥ 𝐹 ]ˡ [ E ᶜ│ᶜ F′ ] = [ E′/E (⊖ 𝐸) ᶜ│ᵥ 𝐹 ]ˡ
   │ᵥᶜ-preserves 𝐸 F [ 𝐸′ │ᵥ 𝐹 ]ˡ [ 𝐸″ │ᵥᶜ F′ ] = [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ ⌣-sym 𝐹 ]
   │ᵥᶜ-preserves 𝐸 F [ 𝐸′ │ᵥᵇ .F ]ˡ [ 𝐸″ ᵇᶜ│ Q ]ˡ = [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥᵇ F ]ˡ
   │ᵥᶜ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ .F ]ˡ [ 𝐸″ ᶜᶜ│ Q ]ˡ = [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥᶜ F ]ˡ
   │ᵥᶜ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   │ᵥᶜ-preserves _ _ [ _ │ᵥ _ ] [ () ]ˡ
   │ᵥᶜ-preserves _ _ [ _ │ᵥᵇ ._ ]ˡ [ () ]
   │ᵥᶜ-preserves _ _ [ _ ᵇ│ᵥ _ ]ˡ [ () ]ˡ
   │ᵥᶜ-preserves _ _ [ _ ᶜ│ᵥ _ ]ˡ [ () ]ˡ
   │ᵥᶜ-preserves _ _ [ _ │ᵥ _ ]ˡ [ () ]ˡ

   │ᵥᶜˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a″ x R R′ R″ S} {a′⌣a″ : a ᶜ ᴬ⌣ a″} {a⌣a″ : τ ᶜ ᴬ⌣ a″}
                  {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ (x •) ᵇ - _ ]→ R′} (𝐸 : E ⌣[ ᶜ∇ᵇ ] E′)
                  (F : Q —[ (• x) ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″}
                  (𝐸′ : E ᶜ│ Q ⌣[ a′⌣a″ ] E″) (𝐸″ : E′ │ᵥ F ⌣[ a⌣a″ ] E″) →
                  νᶜ (E/E′ (⊖ 𝐸) ᶜ│ S) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ │•ᶜ F′ ] [ 𝐸″ │ᵥ• 𝐹 ] = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᶜ E′/E (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ F′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹 ] = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥᶜ E′/E (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ F′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹 ] = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᶜ E′/E (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ E ᶜ│ᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹 ]ˡ = [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵇ E/E′ (⊖ 𝐹) ]ˡ ]ˡ
   │ᵥᶜˡ-preserves 𝐸 F [ E ᶜ│ᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹 ]ˡ = [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᶜ E/E′ (⊖ 𝐹) ]ˡ ]ˡ
   │ᵥᶜˡ-preserves 𝐸 F [ E ᶜ│ᶜ F′ ] [ E′ ᶜ│ᵥ 𝐹 ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᶜ E/E′ (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ F′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹 ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥᶜ E/E′ (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ │ᵥᶜ F′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹 ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │•ᶜ E/E′ (⊖ 𝐹) ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ ᶜᶜ│ Q ] [ 𝐸″ │ᵥᶜ .F ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ _ ] ]
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ ᵇᶜ│ Q ]ˡ [ 𝐸″ │ᵥᵇ .F ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 ᵇᶜ│ _ ] ]ˡ
   │ᵥᶜˡ-preserves 𝐸 F [ 𝐸′ ᶜᶜ│ Q ]ˡ [ 𝐸″ │ᵥᶜ .F ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ _ ] ]
   │ᵥᶜˡ-preserves _ _ [ _ ᶜ│ᵇ _ ] [ () ]
   │ᵥᶜˡ-preserves _ _ [ _ ᶜ│ᶜ _ ] [ () ]
   │ᵥᶜˡ-preserves _ _ [ _ ᶜᶜ│ _ ] [ () ]
   │ᵥᶜˡ-preserves _ _ [ _ │•ᶜ _ ] [ () ]ˡ
   │ᵥᶜˡ-preserves _ _ [ _ ᵇᶜ│ _ ]ˡ [ () ]
   │ᵥᶜˡ-preserves _ _ [ _ ᶜᶜ│ _ ]ˡ [ () ]

   ᵇ│ᵥ-preserves : ∀ {Γ} {P Q : Proc Γ} {x a a″ R R″ S S′} {a⌣a′} {a′⌣a″} {a⌣a″} (E : P —[ (x •) ᵇ - _ ]→ R) →
                  {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} (𝐹 : F ⌣[ a⌣a′ ] F′ )
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E │ᵥ F′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : P │ᵇ F ⌣[ a⌣a″ ] E″) →
                  E′/E (⊖₁ (E ᵇ│ᵥ 𝐹)) ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ 𝐸 │ᵥ• 𝐹′ ] [ E′ ᵇ│• 𝐹″ ] = [ (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ 𝐸 │ᵥ• 𝐹′ ] [ E′ ᵇ│• 𝐹″ ] = [ (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ 𝐸 │ᵥ 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ ⌣-sym (/-preserves-⌣ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ• ⌣-sym (/-preserves-⌣ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ• ⌣-sym (/-preserves-⌣ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ] =
      [ (push *ᵇ) E ᵇ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ] =
      [ (push *ᵇ) E ᵇ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ] =
      [ (push *ᵇ) E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ] =
      [ (push *ᵇ) E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ] =
      [ (push *ᵇ) E ᵇ│• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ] =
      [ (push *ᵇ) E ᵇ│• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ] =
      [ (push *ᵇ) E ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ] =
      [ (push *ᵇ) E ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ .E ᶜ│ᵥ 𝐹′ ]ˡ [ P │ᵇᶜ 𝐹″ ] = [ (push *ᵇ) E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ .E ᶜ│ᵥ 𝐹′ ]ˡ [ P │ᵇᶜ 𝐹″ ] = [ (push *ᵇ) E ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │ᵥ• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) 𝐸 │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ] =
      [ (push *ᵇᵇ⌣) (⌣-sym 𝐸) │• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ 𝐸 │ᵥᵇ F′ ]ˡ [ E′ ᵇ│ᵇ F ]ˡ = [ (push *ᵇᵇ⌣) 𝐸 │ᵥᵇ E′/E (⊖ 𝐹) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ 𝐸 │ᵥᵇ F′ ]ˡ [ E′ ᵇ│ᵇ F ]ˡ = [ (push *ᵇᵇ⌣) 𝐸 │•ᵇ E′/E (⊖ 𝐹) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ 𝐸 │ᵥᶜ F′ ]ˡ [ E′ ᶜ│ᵇ F ]ˡ = [ (push *ᶜᵇ⌣) 𝐸 │ᵥᶜ E′/E (⊖ 𝐹) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ 𝐸 │ᵥᶜ F′ ]ˡ [ E′ ᶜ│ᵇ F ]ˡ = [ (push *ᶜᵇ⌣) 𝐸 │•ᶜ E′/E (⊖ 𝐹) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ .E ᵇ│ᵥ 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᵇ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᵇ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᵇ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹′ ]ˡ [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹″ ]ˡ =
      [ (push *ᵇ) E ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᵇ│ᵥ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   ᵇ│ᵥ-preserves _ _ [ _ │ᵥ _ ] [ () ]ˡ
   ᵇ│ᵥ-preserves _ _ [ _ │ᵥᵇ _ ]ˡ [ () ]
   ᵇ│ᵥ-preserves _ _ [ _ │ᵥᶜ _ ]ˡ [ () ]
   ᵇ│ᵥ-preserves _ _ [ ._ ᶜ│ᵥ _ ]ˡ [ () ]ˡ
   ᵇ│ᵥ-preserves _ _ [ _ │ᵥ _ ]ˡ [ () ]ˡ

   ᵇ│ᵥˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {x a a″ R R″ S S′} {a⌣a′} {a′⌣a″} {a⌣a″} (E : P —[ (x •) ᵇ - _ ]→ R) →
                  {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} (𝐹 : F ⌣[ a⌣a′ ] F′ )
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → P │ᵇ F ⌣[ a′⌣a″ ] E″ → (𝐸″ : E │ᵥ F′ ⌣[ a⌣a″ ] E″) →
                  E/E′ (⊖₁ (E ᵇ│ᵥ 𝐹)) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ E′ ᵇ│• 𝐹′ ] [ 𝐸 │ᵥ• 𝐹″ ] = [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ E′ ᵇ│• 𝐹′ ] [ 𝐸 │ᵥ• 𝐹″ ] = [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ] =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ] =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ] =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ] =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ] =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ] =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ] =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ] =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ νᵇᵇ [ _ │ᵇᵇ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ νᵛᵛ [ _ │ᵇᵇ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ ν•ᵇ [ _ │ᵇᶜ ⌣-sym (/-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ = [ {!!} ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ =
      [ ν•ᵇ [ _ │ᵇᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ]ˡ ]ˡ
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ = [ {!!} ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ = [ {!!} ]ˡ
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ =
      [ ν• [ _ │ᶜᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ P │ᵇᶜ 𝐹′ ] [ .E ᶜ│ᵥ 𝐹″ ]ˡ = [ νᵇᶜ [ _ │ᵇᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ P │ᵇᶜ 𝐹′ ] [ .E ᶜ│ᵥ 𝐹″ ]ˡ = [ ν•ᶜ [ _ │ᶜᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ E′ ᵇ│ᵇ F ]ˡ [ 𝐸 │ᵥᵇ F′ ]ˡ = [ νᵇᵇ [ E/E′ (⊖ 𝐸) ᵇ│ᵇ E/E′ (⊖ 𝐹) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ E′ ᵇ│ᵇ F ]ˡ [ 𝐸 │ᵥᵇ F′ ]ˡ = [ ν•ᵇ [ E/E′ (⊖ 𝐸) ᵇ│ᶜ E/E′ (⊖ 𝐹) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ E′ ᶜ│ᵇ F ]ˡ [ 𝐸 │ᵥᶜ F′ ]ˡ = [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵇ E/E′ (⊖ 𝐹) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ E′ ᶜ│ᵇ F ]ˡ [ 𝐸 │ᵥᶜ F′ ]ˡ = [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᶜ E/E′ (⊖ 𝐹) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ νᵇᵇ [ _ │ᵇᵇ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ ν•ᵇ [ _ │ᵇᶜ ⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ =
      [ νᵛᵛ [ _ │ᵇᵇ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ = [ {!!} ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ =
      [ ν•ᵇ [ _ │ᵇᶜ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]ˡ ]ˡ
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ = [ {!!} ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵇ∇ᵇ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ = [ {!!} ]
   ᵇ│ᵥˡ-preserves {a⌣a′ = ᵛ∇ᵛ} E 𝐹 [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ =
      [ ν• [ _ │ᶜᶜ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᵇ│ᵥˡ-preserves _ _ [ _ │ᵇᵇ _ ] [ () ]
   ᵇ│ᵥˡ-preserves _ _ [ _ │ᵇᶜ _ ] [ () ]
   ᵇ│ᵥˡ-preserves _ _ [ _ ᵇ│• _ ] [ () ]ˡ
   ᵇ│ᵥˡ-preserves _ _ [ _ ᵇ│ᵇ _ ]ˡ [ () ]
   ᵇ│ᵥˡ-preserves _ _ [ _ ᶜ│ᵇ _ ]ˡ [ () ]
   ᵇ│ᵥˡ-preserves _ _ [ _ │ᵇᵇ _ ]ˡ [ () ]

   ᶜ│ᵥ-preserves : ∀ {Γ} {P Q : Proc Γ} {x a a″ R R″ S S′} {a′⌣a″} {a⌣a″} (E : P —[ (x •) ᵇ - _ ]→ R) →
                  {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} (𝐹 : F ⌣[ ᶜ∇ᵇ ] F′ )
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E │ᵥ F′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : P │ᶜ F ⌣[ a⌣a″ ] E″) →
                  E │ᵥ E′/E (⊖ 𝐹) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᶜ│ᵥ-preserves E 𝐹 [ 𝐸 │ᵥ• 𝐹′ ] [ E′ ᶜ│• 𝐹″ ] = [ 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᶜ│ᵥ-preserves E 𝐹 [ 𝐸 │ᵥ 𝐹′ ] [ E′ ᶜ│ᵥ 𝐹″ ] = [ 𝐸 │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   ᶜ│ᵥ-preserves E 𝐹 [ .E ᶜ│ᵥ 𝐹′ ]ˡ [ P │ᶜᶜ 𝐹″ ] = [ E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᶜ│ᵥ-preserves E 𝐹 [ 𝐸 │ᵥ 𝐹′ ]ˡ [ E′ ᶜ│ᵥ 𝐹″ ] = [ ⌣-sym 𝐸 │ᵥ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   ᶜ│ᵥ-preserves E 𝐹 [ 𝐸 │ᵥᵇ F′ ]ˡ [ E′ ᵇ│ᶜ F ]ˡ = [ 𝐸 │ᵥᵇ E′/E (⊖ 𝐹) ]ˡ
   ᶜ│ᵥ-preserves E 𝐹 [ 𝐸 │ᵥᶜ F′ ]ˡ [ E′ ᶜ│ᶜ F ]ˡ = [ 𝐸 │ᵥᶜ E′/E (⊖ 𝐹) ]ˡ
   ᶜ│ᵥ-preserves E 𝐹 [ .E ᵇ│ᵥ 𝐹′ ]ˡ [ P │ᵇᶜ 𝐹″ ]ˡ = [ E ᵇ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᶜ│ᵥ-preserves E 𝐹 [ .E ᶜ│ᵥ 𝐹′ ]ˡ [ P │ᶜᶜ 𝐹″ ]ˡ = [ E ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ
   ᶜ│ᵥ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   ᶜ│ᵥ-preserves _ _ [ _ │ᵥ _ ] [ () ]ˡ
   ᶜ│ᵥ-preserves _ _ [ _ │ᵥᵇ _ ]ˡ [ () ]
   ᶜ│ᵥ-preserves _ _ [ _ │ᵥᶜ _ ]ˡ [ () ]
   ᶜ│ᵥ-preserves _ _ [ ._ ᵇ│ᵥ _ ]ˡ [ () ]
   ᶜ│ᵥ-preserves _ _ [ _ │ᵥ _ ]ˡ [ () ]ˡ

   ᶜ│ᵥˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {x a a″ R R″ S S′} {a′⌣a″} {a⌣a″} (E : P —[ (x •) ᵇ - _ ]→ R) →
                  {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} (𝐹 : F ⌣[ ᶜ∇ᵇ ] F′ )
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → P │ᶜ F ⌣[ a′⌣a″ ] E″ → (𝐸″ : E │ᵥ F′ ⌣[ a⌣a″ ] E″) →
                  (νᶜ (R │ᶜ E/E′ (⊖ 𝐹))) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] (E′/E (⊖ 𝐸″))
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│• 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] = [ νᶜᶜ [ E′/E (⊖ 𝐸″) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] = [ νᶜᶜ [ E′/E (⊖ 𝐸″) ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] = [ νᶜᶜ [ E′/E (⊖ 𝐸″) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸″) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸″) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ P │ᶜᶜ 𝐹′ ] [ .E ᶜ│ᵥ 𝐹″ ]ˡ = [ νᶜᶜ [ _ │ᶜᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᵇ│ᶜ F ]ˡ [ 𝐸″ │ᵥᵇ F′ ]ˡ = [ νᵇᶜ [ E/E′ (⊖ 𝐸″) ᵇ│ᶜ E/E′ (⊖ 𝐹) ] ]ˡ
   ᶜ│ᵥˡ-preserves E 𝐹 [ E′ ᶜ│ᶜ F ]ˡ [ 𝐸″ │ᵥᶜ F′ ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸″) ᶜ│ᶜ E/E′ (⊖ 𝐹) ]ˡ ]
   ᶜ│ᵥˡ-preserves E 𝐹 [ P │ᵇᶜ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″ ]ˡ = [ νᵇᶜ [ _ │ᵇᶜ ⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″) ] ]ˡ
   ᶜ│ᵥˡ-preserves E 𝐹 [ P │ᵇᶜ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″ ]ˡ = [ ν•ᶜ [ _ │ᶜᶜ ⌣-sym (/-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″) ] ]ˡ
   ᶜ│ᵥˡ-preserves E 𝐹 [ P │ᶜᶜ 𝐹′ ]ˡ [ .E ᶜ│ᵥ 𝐹″ ]ˡ = [ νᶜᶜ [ _ │ᶜᶜ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   ᶜ│ᵥˡ-preserves _ _ [ _ │ᶜᶜ _ ] [ () ]
   ᶜ│ᵥˡ-preserves _ _ [ _ ᶜ│• _ ] [ () ]ˡ
   ᶜ│ᵥˡ-preserves _ _ [ _ ᵇ│ᶜ _ ]ˡ [ () ]
   ᶜ│ᵥˡ-preserves _ _ [ _ ᶜ│ᶜ _ ]ˡ [ () ]
   ᶜ│ᵥˡ-preserves _ _ [ _ │ᵇᶜ _ ]ˡ [ () ]
   ᶜ│ᵥˡ-preserves _ _ [ _ │ᶜᶜ _ ]ˡ [ () ]

   │ᵥ-preserves : ∀ {Γ} {P Q : Proc Γ} {x u a″ R R′ R″ S S′} {•x⌣•u} {a′⌣a″} {a⌣a″}
                 {E : P —[ (x •) ᵇ - _ ]→ R} {F : Q —[ (• x) ᵇ - _ ]→ S}
                 {E′ : P —[ (u •) ᵇ - _ ]→ R′} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} {E″ : P │ Q —[ a″ - _ ]→ R″}
                 (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣[ •x⌣•u ] F′) → E′ │ᵥ F′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E │ᵥ F ⌣[ a⌣a″ ] E″) →
                 E′/E (⊖₁ (𝐸 │ᵥ 𝐹)) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ•_ {y = y} 𝐸′ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | _ = [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ•_ {y = y} 𝐸′ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | _ = [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᵁᴰ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᵁᴰ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ᵁᵁᴰ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ᵁᵁᴰ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ 𝐸′ │ᵥᵇ F′ ]ˡ [ 𝐸″ │ᵥᵇ F ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 │ᵥᵇ E′/E (⊖ 𝐹) ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ 𝐸′ │ᵥᵇ F′ ]ˡ [ 𝐸″ │ᵥᵇ F ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 │•ᵇ E′/E (⊖ 𝐹) ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ 𝐸′ │ᵥᶜ F′ ]ˡ [ 𝐸″ │ᵥᶜ F ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 │ᵥᶜ E′/E (⊖ 𝐹) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ 𝐸′ │ᵥᶜ F′ ]ˡ [ 𝐸″ │ᵥᶜ F ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 │•ᶜ E′/E (⊖ 𝐹) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ E′ ᵇ│ᵥ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹″ ]ˡ =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹″ ]ˡ =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹″ ]ˡ =
      [ νᵇᶜ [ E′/E (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ =
      [ ν•ᶜ [ E′/E (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ]ˡ [ E ᶜ│ᵥ 𝐹″ ]ˡ =
      [ νᶜᶜ [ E′/E (⊖ 𝐸) ᶜ│ᵥ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ E′ ᶜ│ᵥ 𝐹′ ]ˡ [ E ᶜ│ᵥ 𝐹″ ]ˡ =
      [ νᶜᶜ [ E′/E (⊖ 𝐸) ᶜ│• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″) │ᵥ• ⌣-sym (/-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″) ]ˡ ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   │ᵥ-preserves _ _ [ _ │ᵥᵇ _ ]ˡ [ () ]
   │ᵥ-preserves _ _ [ _ │ᵥᶜ _ ]ˡ [ () ]
   │ᵥ-preserves _ _ [ _ ᵇ│ᵥ _ ]ˡ [ () ]
   │ᵥ-preserves _ _ [ _ ᶜ│ᵥ _ ]ˡ [ () ]

   │ᵥˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {x u a″ R R′ R″ S S′} {•x⌣•u} {a′⌣a″} {a⌣a″}
                 {E : P —[ (x •) ᵇ - _ ]→ R} {F : Q —[ (• x) ᵇ - _ ]→ S}
                 {E′ : P —[ (u •) ᵇ - _ ]→ R′} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} {E″ : P │ Q —[ a″ - _ ]→ R″}
                 (𝐸 : E ⌣[ ᵇ∇ᵇ ] E′) (𝐹 : F ⌣[ •x⌣•u ] F′) → E │ᵥ F ⌣[ a⌣a″ ] E″ → (𝐸″ : E′ │ᵥ F′ ⌣[ a′⌣a″ ] E″) →
                 E/E′ (⊖₁ (𝐸 │ᵥ 𝐹)) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a⌣a″ a′⌣a″ ] E′/E (⊖ 𝐸″)
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ•_ {y = y} 𝐸′ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | _ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ•_ {y = y} 𝐸′ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | _ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᴰᵁᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᵁᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᴰᵁᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᵁᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᵁᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ] [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᴰᴰᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᴰᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᴰᴰᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ] ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ 𝐸′ │ᵥᵇ F ]ˡ [ 𝐸″ │ᵥᵇ F′ ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥᵇ E/E′ (⊖ 𝐹) ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ 𝐸′ │ᵥᵇ F ]ˡ [ 𝐸″ │ᵥᵇ F′ ]ˡ = [ νᵇᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │•ᵇ E/E′ (⊖ 𝐹) ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ 𝐸′ │ᵥᶜ F ]ˡ [ 𝐸″ │ᵥᶜ F′ ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥᶜ E/E′ (⊖ 𝐹) ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ 𝐸′ │ᵥᶜ F ]ˡ [ 𝐸″ │ᵥᶜ F′ ]ˡ = [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │•ᶜ E/E′ (⊖ 𝐹) ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ E ᵇ│ᵥ 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″ ]ˡ =
      [ νᵇᶜ [ E/E′ (⊖ 𝐸) ᵇ│• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″ ]ˡ =
      [ ν•ᶜ [ E/E′ (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ E ᶜ│ᵥ 𝐹′ ]ˡ [ _ᶜ│ᵥ_ E′ 𝐹″ ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸) ᶜ│ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ E ᶜ│ᵥ 𝐹′ ]ˡ [ E′ ᶜ│ᵥ 𝐹″ ]ˡ = [ νᶜᶜ [ E/E′ (⊖ 𝐸) ᶜ│• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ 𝐸′ │ᵥ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]ˡ ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]ˡ ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹 [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ] ]ˡ
   │ᵥˡ-preserves _ _ [ _ │ᵥ• _ ] [ () ]ˡ
   │ᵥˡ-preserves _ _ [ _ │ᵥᵇ _ ]ˡ [ () ]
   │ᵥˡ-preserves _ _ [ _ │ᵥᶜ _ ]ˡ [ () ]
   │ᵥˡ-preserves _ _ [ _ ᵇ│ᵥ _ ]ˡ [ () ]
   │ᵥˡ-preserves _ _ [ _ ᶜ│ᵥ _ ]ˡ [ () ]

   ᵇᶜ│-preserves : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a″} {a⌣a″}
                  {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} (𝐸 : E ⌣[ ᵇ∇ᶜ ] E′) (Q : Proc Γ) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E′ ᶜ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ᵇ│ Q ⌣[ a⌣a″ ] E″) →
                  E′/E (⊖ 𝐸) ᶜ│ (push *) Q ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇᶜ│-preserves 𝐸 Q [ E′ ᶜ│ᵇ F ] [ E ᵇ│ᵇ .F ] = [ E′/E (⊖ 𝐸) ᶜ│ᵇ (push *ᵇ) F ]
   ᵇᶜ│-preserves 𝐸 Q [ E′ ᶜ│ᶜ F ] [ E ᵇ│ᶜ .F ] = [ E′/E (⊖ 𝐸) ᶜ│ᶜ (push *ᶜ) F ]
   ᵇᶜ│-preserves 𝐸 Q [ _│•ᶜ_ {y = y} 𝐸′ F ] [ _│•ᵇ_ {a = a} 𝐸″ .F ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸″))
   ... | _ rewrite pop∘push y a = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F ]
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ │ᵥᶜ F ] [ 𝐸″ │ᵥᵇ .F ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F ]
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ] [ 𝐸″ ᵇᶜ│ .Q ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q ]
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ .Q ] = [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 ᵇᶜ│ (push *) Q ]ˡ
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ .Q ] = [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q ]
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ]ˡ [ 𝐸″ ᵇᶜ│ .Q ] = [ ⌣-sym (/-preserves-⌣ 𝐸″ 𝐸′ 𝐸) ᶜᶜ│ (push *) Q ]
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 ᵇᶜ│ (push *) Q ]ˡ
   ᵇᶜ│-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 ᶜᶜ│ (push *) Q ]ˡ
   ᵇᶜ│-preserves _ _ [ _ ᶜ│ᵇ _ ] [ () ]ˡ
   ᵇᶜ│-preserves _ _ [ _ ᶜ│ᶜ _ ] [ () ]ˡ
   ᵇᶜ│-preserves _ _ [ _ │•ᶜ _ ] [ () ]ˡ
   ᵇᶜ│-preserves _ _ [ _ │ᵥᶜ _ ] [ () ]ˡ
   ᵇᶜ│-preserves _ _ [ _ ᶜᶜ│ ._ ] [ () ]ˡ
   ᵇᶜ│-preserves _ _ [ _ ᶜᶜ│ ._ ]ˡ [ () ]ˡ

   ᵇᶜ│ˡ-preserves : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a″} {a⌣a″}
                  {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} (𝐸 : E ⌣[ ᵇ∇ᶜ ] E′) (Q : Proc Γ) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E ᵇ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : E′ ᶜ│ Q ⌣[ a⌣a″ ] E″) →
                  E/E′ (⊖ 𝐸) ᵇ│ Q ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇᶜ│ˡ-preserves 𝐸 Q [ E ᵇ│ᵇ F ] [ E′ ᶜ│ᵇ .F ] = [ E/E′ (⊖ 𝐸) ᵇ│ᵇ F ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ E ᵇ│ᶜ F ] [ E′ ᶜ│ᶜ .F ] = [ E/E′ (⊖ 𝐸) ᵇ│ᶜ F ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ _│•ᵇ_ {y = y} 𝐸′ F ] [ _│•ᶜ_ {a = a} 𝐸″ .F ] with (pop y *ᶜ) (E/E′ (⊖ 𝐸″))
   ... | _ rewrite pop∘push y a = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᵇ F ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ │ᵥᵇ F ] [ 𝐸″ │ᵥᶜ .F ] = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥᵇ F ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ] = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᵇᵇ│ .Q ] [ 𝐸″ ᵇᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ Q ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q ]
   ᵇᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᵇᵇ│ .Q ]ˡ [ 𝐸″ ᵇᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ Q ]
   ᵇᶜ│ˡ-preserves _ _ [ _ ᵇᵇ│ ._ ] [ () ]
   ᵇᶜ│ˡ-preserves _ _ [ _ ᵇ│ᵇ _ ] [ () ]ˡ
   ᵇᶜ│ˡ-preserves _ _ [ _ ᵇ│ᶜ _ ] [ () ]ˡ
   ᵇᶜ│ˡ-preserves _ _ [ _ │•ᵇ _ ] [ () ]ˡ
   ᵇᶜ│ˡ-preserves _ _ [ _ │ᵥᵇ _ ] [ () ]ˡ
   ᵇᶜ│ˡ-preserves _ _ [ _ ᵇᵇ│ ._ ]ˡ [ () ]

   ᶜᶜ│-preserves : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a″} {a⌣a″}
                  {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} (𝐸 : E ⌣[ ᶜ∇ᶜ ] E′) (Q : Proc Γ) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E′ ᶜ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ᶜ│ Q ⌣[ a⌣a″ ] E″) →
                  E′/E (⊖ 𝐸) ᶜ│ Q ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᶜᶜ│-preserves 𝐸 Q [ E′ ᶜ│ᵇ F ] [ E ᶜ│ᵇ .F ] = [ E′/E (⊖ 𝐸) ᶜ│ᵇ F ]
   ᶜᶜ│-preserves 𝐸 Q [ E′ ᶜ│ᶜ F ] [ E ᶜ│ᶜ .F ] = [ E′/E (⊖ 𝐸) ᶜ│ᶜ F ]
   ᶜᶜ│-preserves 𝐸 Q [ _│•ᶜ_ {y = y} 𝐸′ F ] [ _│•ᶜ_ {a = a} 𝐸″ .F ] with (pop y *ᶜ) (E/E′ (⊖ 𝐸″))
   ... | _ rewrite pop∘push y a = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᶜ F ]
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ │ᵥᶜ F ] [ 𝐸″ │ᵥᶜ .F ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F ]
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ] = [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ]ˡ = [ /-preserves-⌣ᴰᴰᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ]ˡ [ 𝐸″ ᶜᶜ│ .Q ] = [ /-preserves-⌣ᴰᵁᴰ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ 𝐸″ ᵇᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᴰ 𝐸″ 𝐸′ 𝐸 ᵇᶜ│ Q ]ˡ
   ᶜᶜ│-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ]ˡ [ 𝐸″ ᶜᶜ│ .Q ]ˡ = [ /-preserves-⌣ᴰᵁᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│-preserves _ _ [ _ ᶜ│ᵇ _ ] [ () ]ˡ
   ᶜᶜ│-preserves _ _ [ _ ᶜ│ᶜ _ ] [ () ]ˡ
   ᶜᶜ│-preserves _ _ [ _ │•ᶜ _ ] [ () ]ˡ
   ᶜᶜ│-preserves _ _ [ _ │ᵥᶜ _ ] [ () ]ˡ
   ᶜᶜ│-preserves _ _ [ _ ᵇᶜ│ ._ ]ˡ [ () ]

   ᶜᶜ│ˡ-preserves : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a″} {a⌣a″}
                  {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} (𝐸 : E ⌣[ ᶜ∇ᶜ ] E′) (Q : Proc Γ) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → E ᶜ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : E′ ᶜ│ Q ⌣[ a⌣a″ ] E″) →
                  E/E′ (⊖ 𝐸) ᶜ│ Q ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᶜᶜ│ˡ-preserves 𝐸 Q [ E ᶜ│ᵇ F ] [ E′ ᶜ│ᵇ .F ] = [ E/E′ (⊖ 𝐸) ᶜ│ᵇ F ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ E ᶜ│ᶜ F ] [ E′ ᶜ│ᶜ .F ] = [ E/E′ (⊖ 𝐸) ᶜ│ᶜ F ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ _│•ᶜ_ {y = y} 𝐸′ F ] [ _│•ᶜ_ {a = a} 𝐸″ .F ] with (pop y *ᶜ) (E/E′ (⊖ 𝐸″))
   ... | _ rewrite pop∘push y a = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │•ᶜ F ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ │ᵥᶜ F ] [ 𝐸″ │ᵥᶜ .F ] = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ] = [ /-preserves-⌣ᵁᴰᴰ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ] [ 𝐸″ ᶜᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ]ˡ [ 𝐸″ ᶜᶜ│ .Q ] = [ /-preserves-⌣ᵁᵁᴰ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᵇᶜ│ .Q ]ˡ [ 𝐸″ ᵇᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᴰᵁ 𝐸″ 𝐸′ 𝐸 ᵇᶜ│ Q ]ˡ
   ᶜᶜ│ˡ-preserves 𝐸 Q [ 𝐸′ ᶜᶜ│ .Q ]ˡ [ 𝐸″ ᶜᶜ│ .Q ]ˡ = [ /-preserves-⌣ᵁᵁᵁ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q ]
   ᶜᶜ│ˡ-preserves _ _ [ _ ᶜ│ᵇ _ ] [ () ]ˡ
   ᶜᶜ│ˡ-preserves _ _ [ _ ᶜ│ᶜ _ ] [ () ]ˡ
   ᶜᶜ│ˡ-preserves _ _ [ _ │•ᶜ _ ] [ () ]ˡ
   ᶜᶜ│ˡ-preserves _ _ [ _ │ᵥᶜ _ ] [ () ]ˡ
   ᶜᶜ│ˡ-preserves _ _ [ _ ᵇᶜ│ ._ ]ˡ [ () ]

   │ᶜᶜ-preserves : ∀ {Γ} {Q : Proc Γ} {a a′ a″ S S′ R″} {a′⌣a″} {a⌣a″}
                  (P : Proc Γ) {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} (𝐹 : F ⌣[ ᶜ∇ᶜ ] F′) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → P │ᶜ F′ ⌣[ a′⌣a″ ] E″ → (𝐹″ : P │ᶜ F ⌣[ a⌣a″ ] E″) →
                  P │ᶜ E′/E (⊖ 𝐹) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐹″)
   │ᶜᶜ-preserves P 𝐹 [ E ᶜ│• 𝐹′ ] [ .E ᶜ│• 𝐹″ ] = [ E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves P 𝐹 [ E ᶜ│ᵥ 𝐹′ ] [ .E ᶜ│ᵥ 𝐹″ ] = [ E ᶜ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ] [ .P │ᶜᶜ 𝐹″ ] = [ P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ] [ .P │ᶜᶜ 𝐹″ ]ˡ = [ P │ᶜᶜ /-preserves-⌣ᴰᴰᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ]ˡ [ .P │ᶜᶜ 𝐹″ ] = [ P │ᶜᶜ /-preserves-⌣ᴰᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves P 𝐹 [ E ᵇ│ᶜ F′ ]ˡ [ .E ᵇ│ᶜ F ]ˡ = [ E ᵇ│ᶜ E′/E (⊖ 𝐹) ]ˡ
   │ᶜᶜ-preserves P 𝐹 [ E ᶜ│ᶜ F′ ]ˡ [ .E ᶜ│ᶜ F ]ˡ = [ E ᶜ│ᶜ E′/E (⊖ 𝐹) ]ˡ
   │ᶜᶜ-preserves P 𝐹 [ .P │ᵇᶜ 𝐹′ ]ˡ [ .P │ᵇᶜ 𝐹″ ]ˡ = [ P │ᵇᶜ /-preserves-⌣ᵁᴰᴰ 𝐹″ 𝐹′ 𝐹 ]ˡ
   │ᶜᶜ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ]ˡ [ .P │ᶜᶜ 𝐹″ ]ˡ = [ P │ᶜᶜ /-preserves-⌣ᴰᵁᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜ-preserves _ _ [ _ ᶜ│• _ ] [ () ]ˡ
   │ᶜᶜ-preserves _ _ [ _ ᶜ│ᵥ _ ] [ () ]ˡ
   │ᶜᶜ-preserves _ _ [ _ ᵇ│ᶜ _ ]ˡ [ () ]
   │ᶜᶜ-preserves _ _ [ _ ᶜ│ᶜ _ ]ˡ [ () ]
   │ᶜᶜ-preserves _ _ [ ._ │ᵇᶜ _ ]ˡ [ () ]

   │ᶜᶜˡ-preserves : ∀ {Γ} {Q : Proc Γ} {a a′ a″ S S′ R″} {a′⌣a″} {a⌣a″}
                  (P : Proc Γ) {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} (𝐹 : F ⌣[ ᶜ∇ᶜ ] F′) →
                  {E″ : P │ Q —[ a″ - _ ]→ R″} → P │ᶜ F ⌣[ a′⌣a″ ] E″ → (𝐹″ : P │ᶜ F′ ⌣[ a⌣a″ ] E″) →
                  P │ᶜ E/E′ (⊖ 𝐹) ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐹″)
   │ᶜᶜˡ-preserves P 𝐹 [ E ᶜ│• 𝐹′ ] [ .E ᶜ│• 𝐹″ ] = [ E ᶜ│• /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves P 𝐹 [ E ᶜ│ᵥ 𝐹′ ] [ .E ᶜ│ᵥ 𝐹″ ] = [ E ᶜ│ᵥ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ] [ .P │ᶜᶜ 𝐹″ ] = [ P │ᶜᶜ /-preserves-⌣ᵁᴰᴰ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ] [ .P │ᶜᶜ 𝐹″ ]ˡ = [ P │ᶜᶜ /-preserves-⌣ᵁᴰᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ]ˡ [ .P │ᶜᶜ 𝐹″ ] = [ P │ᶜᶜ /-preserves-⌣ᵁᵁᴰ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves P 𝐹 [ E ᵇ│ᶜ F ]ˡ [ .E ᵇ│ᶜ F′ ]ˡ = [ E ᵇ│ᶜ E/E′ (⊖ 𝐹) ]ˡ
   │ᶜᶜˡ-preserves P 𝐹 [ E ᶜ│ᶜ F ]ˡ [ .E ᶜ│ᶜ F′ ]ˡ = [ E ᶜ│ᶜ E/E′ (⊖ 𝐹) ]ˡ
   │ᶜᶜˡ-preserves P 𝐹 [ .P │ᵇᶜ 𝐹′ ]ˡ [ .P │ᵇᶜ 𝐹″ ]ˡ = [ P │ᵇᶜ /-preserves-⌣ᵁᴰᵁ 𝐹″ 𝐹′ 𝐹 ]ˡ
   │ᶜᶜˡ-preserves P 𝐹 [ .P │ᶜᶜ 𝐹′ ]ˡ [ .P │ᶜᶜ 𝐹″ ]ˡ = [ P │ᶜᶜ /-preserves-⌣ᵁᵁᵁ 𝐹 𝐹′ 𝐹″ ]
   │ᶜᶜˡ-preserves _ _ [ _ ᶜ│• _ ] [ () ]ˡ
   │ᶜᶜˡ-preserves _ _ [ _ ᶜ│ᵥ _ ] [ () ]ˡ
   │ᶜᶜˡ-preserves _ _ [ _ ᵇ│ᶜ _ ]ˡ [ () ]
   │ᶜᶜˡ-preserves _ _ [ _ ᶜ│ᶜ _ ]ˡ [ () ]
   │ᶜᶜˡ-preserves _ _ [ ._ │ᵇᶜ _ ]ˡ [ () ]

   ᵇ│ᵇ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a′ a″ R R″ S} {a′⌣a″} {a⌣a″}
                  (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″} →
                  P │ᵇ F ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ᵇ│ Q ⌣[ a⌣a″ ] E″) →
                  R │ᵇ (push *ᵇ) F ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᵇ-preserves E F [ _ᵇ│•_ {y = y} E′ 𝐹 ] [ _│•ᵇ_ {a = a} 𝐸 F′ ] with (pop y *ᵇ) (E/E′ (⊖ 𝐸))
   ... | _ rewrite pop∘push y a = [ E′/E (⊖ 𝐸) ᵇ│• (push *ᵇᶜ⌣) 𝐹 ]
   ᵇ│ᵇ-preserves E F [ E′ ᵇ│ᵥ 𝐹 ] [ 𝐸 │ᵥᵇ F′ ] = [ E′/E (⊖ 𝐸) ᵇ│ᵥ (push *ᵇᵇ⌣) 𝐹 ]
   ᵇ│ᵇ-preserves E F [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹 ] [ .E ᵇ│ᵇ F′ ] = [ _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹 ]
   ᵇ│ᵇ-preserves E F [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹 ] [ .E ᵇ│ᵇ F′ ] = [ _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹 ]
   ᵇ│ᵇ-preserves E F [ P │ᵇᶜ 𝐹 ] [ .E ᵇ│ᶜ F′ ] = [ _ │ᵇᶜ (push *ᵇᶜ⌣) 𝐹 ]
   ᵇ│ᵇ-preserves E F [ E′ ᵇ│ᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸 Q ] = [ E′/E (⊖ 𝐸) ᵇ│ᵇ (push *ᵇ) F ]ˡ
   ᵇ│ᵇ-preserves E F [ E′ ᵇ│ᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸 Q ] = [ E′/E (⊖ 𝐸) ᶜ│ᵇ (push *ᵇ) F ]ˡ
   ᵇ│ᵇ-preserves E F [ E′ ᶜ│ᵇ .F ]ˡ [ 𝐸 ᵇᶜ│ Q ] = [ E′/E (⊖ 𝐸) ᶜ│ᵇ (push *ᵇ) F ]ˡ
   ᵇ│ᵇ-preserves E F [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹 ]ˡ [ .E ᵇ│ᵇ F′ ] = [ _ │ᵇᵇ ⌣-sym ((push *ᵇᵇ⌣) 𝐹) ]
   ᵇ│ᵇ-preserves E F [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹 ]ˡ [ .E ᵇ│ᵇ F′ ] = [ _ │ᵇᵇ ⌣-sym ((push *ᵇᵇ⌣) 𝐹) ]
   ᵇ│ᵇ-preserves E F [ E′ ᵇ│ᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸 Q ]ˡ = [ E/E′ (⊖ 𝐸) ᵇ│ᵇ (push *ᵇ) F ]ˡ
   ᵇ│ᵇ-preserves E F [ E′ ᵇ│ᵇ .F ]ˡ [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸 Q ]ˡ = [ E/E′ (⊖ 𝐸) ᶜ│ᵇ (push *ᵇ) F ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ ᵇ│• _ ] [ () ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ ᵇ│ᵥ _ ] [ () ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ │ᵇᵇ _ ] [ () ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ │ᵇᶜ _ ] [ () ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ ᶜ│ᵇ ._ ]ˡ [ () ]ˡ
   ᵇ│ᵇ-preserves _ _ [ _ │ᵇᵇ _ ]ˡ [ () ]ˡ

   ᵇ│ᵇˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a′ a″ R R″ S} {a′⌣a″} {a⌣a″}
                  (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″} →
                  E ᵇ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : P │ᵇ F ⌣[ a⌣a″ ] E″) →
                  (push *ᵇ) E ᵇ│ S ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᵇˡ-preserves E F [ .E ᵇ│ᵇ F′ ] [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹 ] = [ (push *ᵇ) E ᵇ│ᵇ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ .E ᵇ│ᵇ F′ ] [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹 ] = [ (push *ᵇ) E ᵇ│ᶜ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ .E ᵇ│ᶜ F′ ] [ P │ᵇᶜ 𝐹 ] = [ (push *ᵇ) E ᵇ│ᶜ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ 𝐸 │•ᵇ F′ ] [ E′ ᵇ│• 𝐹 ] = [ (push *ᵇᵇ⌣) 𝐸 │•ᵇ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ 𝐸 │ᵥᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹 ] = [ (push *ᵇᵇ⌣) 𝐸 │ᵥᵇ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ 𝐸 │ᵥᵇ F′ ] [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹 ] = [ (push *ᵇᵇ⌣) 𝐸 │•ᵇ E′/E (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ .E ᵇ│ᵇ F′ ] [ _│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} P 𝐹 ]ˡ = [ (push *ᵇ) E ᵇ│ᵇ E/E′ (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ .E ᵇ│ᵇ F′ ] [ _│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} P 𝐹 ]ˡ = [ (push *ᵇ) E ᵇ│ᶜ E/E′ (⊖ 𝐹) ]
   ᵇ│ᵇˡ-preserves E F [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸 Q ] [ E′ ᵇ│ᵇ .F ]ˡ = [ (push *ᵇᵇ⌣) 𝐸 ᵇᵇ│ _ ]
   ᵇ│ᵇˡ-preserves E F [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸 Q ] [ E′ ᵇ│ᵇ .F ]ˡ = [ (push *ᵇᵇ⌣) 𝐸 ᵇᵇ│ _ ]
   ᵇ│ᵇˡ-preserves E F [ 𝐸 ᵇᶜ│ Q ] [ E′ ᶜ│ᵇ .F ]ˡ = [ (push *ᵇᶜ⌣) 𝐸 ᵇᶜ│ _ ]
   ᵇ│ᵇˡ-preserves E F [ _ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸 Q ]ˡ [ E′ ᵇ│ᵇ .F ]ˡ = [ ⌣-sym ((push *ᵇᵇ⌣) 𝐸) ᵇᵇ│ _ ]
   ᵇ│ᵇˡ-preserves E F [ _ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸 Q ]ˡ [ E′ ᵇ│ᵇ .F ]ˡ = [ ⌣-sym ((push *ᵇᵇ⌣) 𝐸) ᵇᵇ│ _ ]
   ᵇ│ᵇˡ-preserves _ _ [ _ ᵇᵇ│ _ ] [ () ]
   ᵇ│ᵇˡ-preserves _ _ [ _ ᵇᶜ│ _ ] [ () ]
   ᵇ│ᵇˡ-preserves _ _ [ ._ ᵇ│ᶜ _ ] [ () ]ˡ
   ᵇ│ᵇˡ-preserves _ _ [ _ │•ᵇ _ ] [ () ]ˡ
   ᵇ│ᵇˡ-preserves _ _ [ _ │ᵥᵇ _ ] [ () ]ˡ
   ᵇ│ᵇˡ-preserves _ _ [ _ ᵇᵇ│ _ ]ˡ [ () ]
-}

   ᵇ│ᶜ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a′ a″ R R″ S} {a′⌣a″} {a⌣a″}
                  (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″} →
                  P │ᶜ F ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ᵇ│ Q ⌣[ a⌣a″ ] E″) →
                  R │ᶜ (push *ᶜ) F ⌣[ /-preserves-ᴬ⌣ ᵇ∇ᶜ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᶜ-preserves E F 𝐸 𝐸′ = {!!}

   ᵇ│ᶜˡ-preserves : ∀ {Γ} {P Q : Proc Γ} {a a′ a″ R R″ S} {a′⌣a″} {a⌣a″}
                  (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) {E″ : P │ Q —[ a″ - _ ]→ R″} →
                  E ᵇ│ Q ⌣[ a′⌣a″ ] E″ → (𝐸″ : P │ᶜ F ⌣[ a⌣a″ ] E″) →
                  E ᵇ│ S ⌣[ /-preserves-ᴬ⌣ ᶜ∇ᵇ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)
   ᵇ│ᶜˡ-preserves E F 𝐸 𝐸′ = {!!}

{-
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] = │ᵥ•-preserves 𝐸 𝐹
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ]ˡ = │ᵥ•ˡ-preserves 𝐸 𝐹
   /-preserves-⌣ [ 𝐸 │ᵥᵇ F ] = │ᵥᵇ-preserves 𝐸 F
   /-preserves-⌣ [ 𝐸 │ᵥᵇ F ]ˡ = │ᵥᵇˡ-preserves 𝐸 F
   /-preserves-⌣ [ 𝐸 │ᵥᶜ F ] = │ᵥᶜ-preserves 𝐸 F
   /-preserves-⌣ [ 𝐸 │ᵥᶜ F ]ˡ = │ᵥᶜˡ-preserves 𝐸 F
   /-preserves-⌣ [ E ᵇ│ᵥ 𝐹 ] = ᵇ│ᵥ-preserves E 𝐹
   /-preserves-⌣ [ E ᵇ│ᵥ 𝐹 ]ˡ = ᵇ│ᵥˡ-preserves E 𝐹
   /-preserves-⌣ [ E ᶜ│ᵥ 𝐹 ] = ᶜ│ᵥ-preserves E 𝐹
   /-preserves-⌣ [ E ᶜ│ᵥ 𝐹 ]ˡ = ᶜ│ᵥˡ-preserves E 𝐹
   /-preserves-⌣ [ 𝐸 │ᵥ 𝐹 ] = │ᵥ-preserves 𝐸 𝐹
   /-preserves-⌣ [ 𝐸 │ᵥ 𝐹 ]ˡ = │ᵥˡ-preserves 𝐸 𝐹
   /-preserves-⌣ [ 𝐸 ᵇᶜ│ Q ] = ᵇᶜ│-preserves 𝐸 Q
   /-preserves-⌣ [ 𝐸 ᵇᶜ│ Q ]ˡ = ᵇᶜ│ˡ-preserves 𝐸 Q
   /-preserves-⌣ [ 𝐸 ᶜᶜ│ Q ] = ᶜᶜ│-preserves 𝐸 Q
   /-preserves-⌣ [ 𝐸 ᶜᶜ│ Q ]ˡ = ᶜᶜ│ˡ-preserves 𝐸 Q
   /-preserves-⌣ [ P │ᶜᶜ 𝐹 ] = │ᶜᶜ-preserves P 𝐹
   /-preserves-⌣ [ P │ᶜᶜ 𝐹 ]ˡ = │ᶜᶜˡ-preserves P 𝐹
   /-preserves-⌣ [ E ᵇ│ᵇ F ] = ᵇ│ᵇ-preserves E F
   /-preserves-⌣ [ E ᵇ│ᵇ F ]ˡ = ᵇ│ᵇˡ-preserves E F
   /-preserves-⌣ [ E ᵇ│ᶜ F ] = ᵇ│ᶜ-preserves E F
-}

   /-preserves-⌣ [ E ᵇ│ᶜ F ]ˡ = ᵇ│ᶜˡ-preserves E F

{-
   /-preserves-⌣ (E ᵇ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᶜᵇ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• (push *ᶜᶜ⌣) 𝐹′
   /-preserves-⌣ (E ᵇ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ (push *ᶜᵇ⌣) 𝐹
   /-preserves-⌣ (E ᵇ│ᶜ F) (P │ᶜᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᶜᶜ (push *ᶜᶜ⌣) 𝐹

   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᶜ_ {y = y} {a = a} 𝐸″ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = E′/E (⊖₁ 𝐸″) ᵇ│• 𝐹′
   /-preserves-⌣ (E ᶜ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ 𝐹
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᶜ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᵇᵇ 𝐹
   /-preserves-⌣ (E ᶜ│ᵇ F) (P │ᵇᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᵇᶜ 𝐹′

   /-preserves-⌣ (E ᶜ│ᶜ F) (P │ᶜᵇ 𝐹) (.E ᶜ│ᵇ F′) = _ │ᶜᵇ 𝐹
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│• 𝐹) (_│•ᶜ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᶜ│• 𝐹
   /-preserves-⌣ (E ᶜ│ᶜ F) (E′ ᶜ│ᵥ 𝐹) (𝐸 │ᵥᶜ F′) = E′/E (⊖₁ 𝐸) ᶜ│ᵥ 𝐹
   /-preserves-⌣ (E ᶜ│ᶜ F) (P │ᶜᶜ 𝐹′) (.E ᶜ│ᶜ F′) = _ │ᶜᶜ 𝐹′

   /-preserves-⌣ (𝐸 ➕₁ Q) (𝐸′ ➕₁ .Q) (𝐸″ ➕₁ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᵇ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᵇ F) (E′ ᵇ│ᵇ .F) = _ ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᵇ│ᶜ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (E ᵇ│ᶜ F) (E′ ᵇ│ᶜ .F) = _ ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᵇ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵇ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ │•ᵇ F) (𝐸″ │•ᵇ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) =
      /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵇ∇ᵇ} {ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {ᵛ∇ᵛ} {ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᵇᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ (push *) Q
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (𝐸 ᵇᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᵇ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᵇ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) =
      (push *ᵇ) E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᵇᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵇ∇ᵇ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} {a′⌣a″ = ᵛ∇ᵛ} {a⌣a″ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᵇᵇ 𝐹″) =
      (push *) P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵇ∇ᵇ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᵇᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ {a⌣a′ = ᵛ∇ᵛ} (P │ᵇᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) (𝐸′ │• 𝐹) (_│•ᵇ_ {y = z} {a = .a} 𝐸″ F′)
      with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸)) | (pop z *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E′ | pop-y*E/E″ rewrite pop∘push y a | pop∘push z a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• (push *ᶜᶜ⌣) 𝐹
   /-preserves-⌣ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) (𝐸′ │•ᵥ 𝐹) (𝐸″ │ᵥᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵥ (push *ᶜᵇ⌣) 𝐹

   /-preserves-⌣ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) (_│•_ {x = x} {.y} {u} {z} 𝐸′ 𝐹) (𝐸″ │•ᶜ F′)
      with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸)) | (pop y *ᵇ) (E′/E (⊖₁ 𝐸′)) | (pop z *ᵇ) (E/E′ (⊖₁ 𝐸′)) | (pop z *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E′ | pop-y*E″/E′ | pop-z*E′/E″ | pop-z*E/E″
      rewrite pop∘push y a | pop∘push u y | pop∘push x z | pop∘push z a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• 𝐹
   /-preserves-⌣ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │ᵥᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵥ 𝐹′

   /-preserves-⌣ (E ᵇ│• 𝐹) (𝐸 │• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (E ᵇ│• 𝐹) (𝐸 │•ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) = (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (E ᶜ│• 𝐹) (𝐸′ │• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸′ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (E ᶜ│• 𝐹) (𝐸′ │•ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (𝐸 │• 𝐹) (𝐸′ │• 𝐹′) (𝐸″ │• 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″) │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (𝐸 │• 𝐹) (𝐸′ │•ᵥ 𝐹′) (𝐸″ │•ᵥ 𝐹″) = (pop _ *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″) │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (ν• 𝐸) (ν• 𝐸′) (ν• 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (ν• 𝐸) (ν•ᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (ν• 𝐸) (ν•ᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣ (ν•ᵇ 𝐸) (νᵇᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (ν•ᵇ 𝐸) (νᵛᵛ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (ν•ᵇ 𝐸) (νᵇᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣ (ν•ᶜ 𝐸) (νᶜᶜ 𝐸′) (ν•ᶜ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (ν•ᶜ 𝐸) (νᶜᵇ 𝐸′) (ν•ᵇ 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᵇ_ {a′ = a′} 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push x | swap∘push∘push a | swap∘push∘push a′ =
      νᵇᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • y} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = y •} 𝐸″) = νᵇᵇ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = u •} 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {a′ = • u} 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = x •} 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″) = νᵛᵛ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = • x} 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″) = νᵛᵛ (swap *ᵇᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = νᵇᶜ (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵇᵇ_ {a = x •} {a} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a | swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {u •} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᵇ_ {a = • x} {• u} 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᵇ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᵇᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᵇᶜ swap*E′/𝐸″/E

   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᵇᵇ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵛᵛ 𝐸′) (νᵛᵛ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵇᶜ_ {a′ = a′} 𝐸′) (νᵇᶜ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = x •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵇᵇ_ {a′ = • x} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵛᵛ 𝐸) (νᵇᵇ 𝐸′) (νᵛᵛ 𝐸″) = νᶜᶜ (swap *ᶜᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)

   /-preserves-⌣ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᶜ 𝐸′) (νᵇᶜ_ {a′ = a″} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) | (swap *ᶜᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ | swap∘push∘push a″ = νᶜᶜ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᶜ 𝐸) (νᶜᵇ_ {a = a} {a′} 𝐸′) (νᵇᵇ_ {a = x •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a | swap∘push∘push a′ =
      νᶜᵇ swap*E′/𝐸″/E

   /-preserves-⌣ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵇᵇ_ {a = • x} {u •} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵇᵇ_ {a = • x} {• u} 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᵇ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᵇ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᵇ swap*E′/𝐸″/E
   /-preserves-⌣ (νᵇᶜ_ {a′ = a′} 𝐸) (νᶜᵇ 𝐸′) (νᵛᵛ 𝐸″)
      with (swap *ᶜ) (E′/E (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″)) | (swap *ᶜ) (E′/E (⊖₁ 𝐸″)) |
           (swap *ᶜᶜ⌣) (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)
   ... | swap*E′/E | swap*E/E″ | swap*E″/E | swap*E′/𝐸″/E rewrite swap∘push∘push a′ = νᶜᶜ swap*E′/𝐸″/E

   /-preserves-⌣ (νᶜᵇ_ {a = a} 𝐸) (νᵇᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νᵇᵇ /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (νᶜᵇ_ {a = a} 𝐸) (νᵛᵛ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸)) | (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E′ | swap*E/E″ rewrite swap∘push∘push a = νᵛᵛ /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (νᶜᵇ_ {a = a} 𝐸) (νᵇᶜ 𝐸′) (νᶜᶜ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | swap*E/E′ rewrite swap∘push∘push a = νᵇᶜ /-preserves-⌣ 𝐸 𝐸′ 𝐸″

   /-preserves-⌣ (νᶜᶜ 𝐸) (νᶜᶜ 𝐸′) (νᶜᶜ 𝐸″) = νᶜᶜ /-preserves-⌣ 𝐸 𝐸′ 𝐸″
   /-preserves-⌣ (νᶜᶜ_ {a = a} 𝐸) (νᶜᵇ 𝐸′) (νᶜᵇ 𝐸″) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | swap*E/E″ rewrite swap∘push∘push a = νᶜᵇ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″)

   /-preserves-⌣ (! 𝐸) (! 𝐸′) (! 𝐸″) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″
-}
   /-preserves-⌣ _ _ _ = {!!}
