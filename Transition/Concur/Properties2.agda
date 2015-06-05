module Transition.Concur.Properties2 where

   open import SharedModules
   open import Ext

   open import Action as ᴬ using (Action; _ᴬ⌣_; ᴬ⌣-sym); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ._ᴬ⌣_
   open import Proc as ᴾ using (Proc)
   open import Ren as ᴿ using (Ren; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_
   open import Transition.Ren
   open import Transition.Concur2
      using (
         Concur; Concur₁; module Concur; module Concur₁; Delta′; module Delta′; Delta;
         ⊖; ⊖₁; ⌣-sym; /-preserves-sym
      );
      open Concur; open Concur₁; open Delta′
   open import Transition.Concur.Ren2 using (/-preserves-ᴬ⌣; _*ᵇᵇ⌣; _*ᵇᶜ⌣; _*ᶜᵇ⌣; _*ᶜᶜ⌣)

   /-preserves-⌣₂ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a″⌣a′ : a″ ᴬ⌣ a′} {a″⌣a : a″ ᴬ⌣ a}
                    {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                    (𝐸 : E ⌣[ a⌣a′ ] E′) → E″ ⌣[ a″⌣a′ ] E′ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                    E/E′ (⊖ 𝐸″) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a″⌣a) a″⌣a′ a⌣a′ ] E′/E (⊖ 𝐸)
   /-preserves-⌣₃ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a′⌣a : a′ ᴬ⌣ a} {a′⌣a″ : a′ ᴬ⌣ a″} {a″⌣a : a″ ᴬ⌣ a}
                    {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                    (𝐸 : E′ ⌣[ a′⌣a ] E) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E″ ⌣[ a″⌣a ] E) →
                    E/E′ (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a) a′⌣a″ (ᴬ⌣-sym a″⌣a) ] E/E′ (⊖ 𝐸″)
   /-preserves-⌣₄ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                    {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″} →
                    E ⌣[ a⌣a′ ] E′ → (𝐸′ : E′ ⌣[ a′⌣a″ ] E″) (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                    E/E′ (⊖ 𝐸′) ⌣[ /-preserves-ᴬ⌣ (ᴬ⌣-sym a′⌣a″) (ᴬ⌣-sym a⌣a′) (ᴬ⌣-sym a⌣a″) ] E/E′ (⊖ 𝐸″)
   /-preserves-⌣ : ∀ {Γ} {P : Proc Γ} {a a′ a″ R R′ R″} {a⌣a′ : a ᴬ⌣ a′} {a′⌣a″ : a′ ᴬ⌣ a″} {a⌣a″ : a ᴬ⌣ a″}
                   {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} {E″ : P —[ a″ - _ ]→ R″}
                   (𝐸 : E ⌣[ a⌣a′ ] E′) → E′ ⌣[ a′⌣a″ ] E″ → (𝐸″ : E ⌣[ a⌣a″ ] E″) →
                   E′/E (⊖ 𝐸) ⌣[ /-preserves-ᴬ⌣ a⌣a′ a′⌣a″ a⌣a″ ] E′/E (⊖ 𝐸″)

   /-preserves-⌣₂ 𝐸 𝐸′ 𝐸″ = {!!}

   /-preserves-⌣₃ 𝐸 𝐸′ 𝐸″ = {!!}

   /-preserves-⌣₄ 𝐸 𝐸′ 𝐸″ = {!!}

   -- Residuation preserves concurrency. There is an unpleasant case-explosion here because of the need to
   -- distinguish the ᵛ∇ᵛ and ᵇ∇ᵇ cases pairwise across the three transitions.
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │• 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ] = [ νᶜᶜ [ /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″ ] ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │• 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸 (⌣-sym 𝐸′) 𝐸″ │• /-preserves-⌣ 𝐹 (⌣-sym 𝐹′) 𝐹″ ] ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 │ᵥ• /-preserves-⌣ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ] =
      [ νᶜᶜ [ /-preserves-⌣ 𝐸″ 𝐸′ 𝐸 │• /-preserves-⌣ 𝐹″ 𝐹′ 𝐹 ]ˡ ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │•ᵇ F ]ˡ [ 𝐸″ │ᵥᵇ F′ ]ˡ = [ νᵇᶜ [ /-preserves-⌣₂ 𝐸 𝐸′ 𝐸″ │•ᵇ _ ] ]ˡ
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │•ᶜ F ]ˡ [ 𝐸″ │ᵥᶜ F′ ]ˡ = [ νᶜᶜ [ /-preserves-⌣₂ 𝐸 𝐸′ 𝐸″ │•ᶜ _ ]ˡ ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ E′ ᵇ│• 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹″ ]ˡ = [ νᵇᶜ [ _ ᵇ│• /-preserves-⌣₂ 𝐹 𝐹′ 𝐹″ ] ]ˡ
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ E′ ᵇ│• 𝐹′ ]ˡ [ _ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹″ ]ˡ = [ ν•ᶜ [ _ ᶜ│• /-preserves-⌣₂ 𝐹 𝐹′ 𝐹″ ] ]ˡ
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ E′ ᶜ│• 𝐹′ ]ˡ [ E ᶜ│ᵥ 𝐹″ ]ˡ = [ νᶜᶜ [ _ ᶜ│• /-preserves-⌣₂ 𝐹 𝐹′ 𝐹″ ]ˡ ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ /-preserves-⌣₂ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣₂ 𝐹 𝐹′ 𝐹″ ]ˡ ]
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ] [ 𝐸′ │ᵥ• 𝐹′ ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″ ]ˡ =
      [ νᶜᶜ [ ⌣-sym (/-preserves-⌣₂ 𝐸 𝐸′ 𝐸″) │• ⌣-sym (/-preserves-⌣₂ 𝐹 𝐹′ 𝐹″) ] ]
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ 𝐸′ │ᵥ• 𝐹′ ] [ 𝐸″ │• 𝐹″ ] =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣₂ 𝐸″ 𝐸′ 𝐸) │ᵥ• /-preserves-⌣₂ 𝐹″ 𝐹′ 𝐹 ]
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ 𝐸′ │ᵥ• 𝐹′ ] [ 𝐸″ │• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣₃ 𝐸 𝐸′ 𝐸″) │ᵥ• /-preserves-⌣₃ 𝐹 𝐹′ 𝐹″ ]
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ 𝐸′ │ᵥ 𝐹′ ] [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣₃ 𝐸 𝐸′ 𝐸″) │ᵥ /-preserves-⌣₃ 𝐹 𝐹′ 𝐹″ ]
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ _│ᵥᵇ_ {a = a} 𝐸′ F ]ˡ [ 𝐸″ │•ᵇ F′ ]ˡ
      with (pop y *ᵇ) (E/E′ (⊖ 𝐸)) | (pop y *ᵇ) (E/E′ (⊖ 𝐸″)) | (pop y *ᵇᵇ⌣) (⌣-sym (/-preserves-⌣₄ 𝐸′ 𝐸 𝐸″))
   ... | _ | _ | pop-y*E/E″⌣E/E′ rewrite pop∘push y a = [ pop-y*E/E″⌣E/E′ │ᵥᵇ _ ]ˡ
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ _│ᵥᶜ_ {a = a} 𝐸′ F ]ˡ [ 𝐸″ │•ᶜ F′ ]ˡ
      with (pop y *ᵇ) (E/E′ (⊖ 𝐸)) | (pop y *ᶜ) (E/E′ (⊖ 𝐸″)) | (pop y *ᶜᵇ⌣) (⌣-sym (/-preserves-⌣₄ 𝐸′ 𝐸 𝐸″))
   ... | _ | _ | pop-y*E/E″⌣E/E′ rewrite pop∘push y a = [ pop-y*E/E″⌣E/E′ │ᵥᶜ _ ]ˡ
   /-preserves-⌣ [ _│ᵥ•_ {x = x} {y = y} 𝐸 𝐹 ]ˡ [ E ᵇ│ᵥ 𝐹′ ]ˡ [ E′ ᵇ│• 𝐹″ ]ˡ with (pop y *ᵇ) (E/E′ (⊖ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y (x •) = [ pop-y*E/E′ ᵇ│ᵥ ⌣-sym (/-preserves-⌣₄ 𝐹′ 𝐹 𝐹″) ]ˡ
   /-preserves-⌣ [ 𝐸 │ᵥ• 𝐹 ]ˡ [ E ᶜ│ᵥ 𝐹′ ]ˡ [ E′ ᶜ│• 𝐹″ ]ˡ = [ _ ᶜ│ᵥ ⌣-sym (/-preserves-⌣₄ 𝐹′ 𝐹 𝐹″) ]ˡ
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ _│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣₄ 𝐸′ 𝐸 𝐸″) │ᵥ /-preserves-⌣₄ 𝐹′ 𝐹 𝐹″ ]
   /-preserves-⌣ [ _│ᵥ•_ {y = y} 𝐸 𝐹 ]ˡ [ _│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′ ]ˡ [ 𝐸″ │ᵥ• 𝐹″ ]ˡ =
      [ (pop y *ᵇᵇ⌣) (/-preserves-⌣₄ 𝐸′ 𝐸 𝐸″) │ᵥ /-preserves-⌣₄ 𝐹′ 𝐹 𝐹″ ]
{-
   /-preserves-⌣ (_│ᵥᵇ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᵇ F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣ (𝐸 │ᵥᵇ F) (𝐸′ │ᵥ 𝐹) (𝐸″ │ᵥᵇ F′) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ (push *ᵇᵇ⌣) 𝐹

   /-preserves-⌣ (_│ᵥᶜ_ {a = a} 𝐸 F) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │•ᶜ F′) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = (/-preserves-⌣ 𝐸 𝐸′ 𝐸″) │ᵥ• 𝐹′
   /-preserves-⌣ (𝐸 │ᵥᶜ F) (𝐸′ │ᵥ 𝐹′) (𝐸″ │ᵥᶜ F′) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ 𝐹′

   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (𝐸′ │ᵥ• 𝐹′) (E′ ᵇ│• 𝐹″) = (push *ᵇᵇ⌣) 𝐸′ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ• (/-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} E′ 𝐹″) =
      (push *ᵇᵇ⌣) 𝐸 │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (E ᶜ│ᵥ 𝐹) (𝐸 │ᵥ• 𝐹′) (E′ ᶜ│• 𝐹″) = 𝐸 │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (E ᶜ│ᵥ 𝐹) (𝐸′ │ᵥ 𝐹′) (E′ ᶜ│ᵥ 𝐹″) = 𝐸′ │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ•_ {y = y} 𝐸′ 𝐹′) (𝐸″ │ᵥ• 𝐹″) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸′))
   ... | pop-y*E′/E″ = νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (𝐸′ │ᵥ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥ• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″)
   /-preserves-⌣ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸′ 𝐹′) (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸″ 𝐹″) =
      νᶜᶜ (/-preserves-⌣ 𝐸 𝐸′ 𝐸″ │• /-preserves-⌣ 𝐹 𝐹′ 𝐹″)

   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᵇ F) (E ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᵇ F
   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (E′ ᵇ│ᶜ F) (E ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᵇ│ᶜ F
   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (𝐸′ │•ᵇ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᵇ F
   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (𝐸′ │ᵥᵇ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᵇ F
   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᵇ│ Q
   /-preserves-⌣ (𝐸 ᶜᵇ│ Q) (𝐸′ ᵇᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᵇᶜ│ Q

   /-preserves-⌣ (P │ᶜᵇ 𝐹) (E ᵇ│• 𝐹′) (.E ᶜ│• 𝐹″) = E ᵇ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᵇ 𝐹) (E ᵇ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᵇ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᵇ 𝐹) (.P │ᵇᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᵇᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᵇ 𝐹) (.P │ᵇᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᵇᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {a⌣a′ = ᵇ∇ᵇ} 𝐸″ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ (push *) Q
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (_ᵇᵇ│_ {a⌣a′ = ᵛ∇ᵛ} 𝐸″ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᵇ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ (push *ᵇ) F
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᵇ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ (push *ᶜ) F
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᵇ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᶜ (push *ᵇ) F
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᵇ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᶜ (push *ᶜ) F
   /-preserves-⌣ (𝐸 ᵇᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᵇᶜ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ (push *) Q

   /-preserves-⌣ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {a⌣a′ = ᵇ∇ᵇ} .P 𝐹″) = (push *) P │ᶜᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᵇᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (_│ᵇᵇ_ {a⌣a′ = ᵛ∇ᵛ} .P 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᵇᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᵇ│• 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵇ∇ᵇ} .E 𝐹″) = (push *ᵇ) E ᶜ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᵇᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (_ᵇ│ᵥ_ {a⌣a′ = ᵛ∇ᵛ} .E 𝐹″) = (push *ᵇ) E ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᵇᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᵇᶜ 𝐹″) = (push *) P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᵇ│ .Q) (𝐸″ ᶜᵇ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᵇ│ Q
   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᵇ F) (E′ ᶜ│ᵇ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᵇ F
   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (E ᶜ│ᶜ F) (E′ ᶜ│ᶜ .F) = E′/E (⊖₁ 𝐸) ᶜ│ᶜ F
   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (𝐸′ │•ᶜ F) (_│•ᶜ_ {y = y} {a = a} 𝐸″ .F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸″))
   ... | pop-y*E/E″ rewrite pop∘push y a = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │•ᶜ F
   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (𝐸′ │ᵥᶜ F) (𝐸″ │ᵥᶜ .F) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ │ᵥᶜ F
   /-preserves-⌣ (𝐸 ᶜᶜ│ Q) (𝐸′ ᶜᶜ│ .Q) (𝐸″ ᶜᶜ│ .Q) = /-preserves-⌣ 𝐸 𝐸′ 𝐸″ ᶜᶜ│ Q

   /-preserves-⌣ (P │ᶜᶜ 𝐹) (.P │ᶜᵇ 𝐹′) (.P │ᶜᵇ 𝐹″) = P │ᶜᵇ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᶜ 𝐹) (E ᶜ│• 𝐹′) (.E ᶜ│• 𝐹″) = _ ᶜ│• /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᶜ 𝐹) (E ᶜ│ᵥ 𝐹′) (.E ᶜ│ᵥ 𝐹″) = E ᶜ│ᵥ /-preserves-⌣ 𝐹 𝐹′ 𝐹″
   /-preserves-⌣ (P │ᶜᶜ 𝐹) (.P │ᶜᶜ 𝐹′) (.P │ᶜᶜ 𝐹″) = P │ᶜᶜ /-preserves-⌣ 𝐹 𝐹′ 𝐹″

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
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│• 𝐹′) (_│•ᵇ_ {y = y} {a = a} 𝐸 F′) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | pop-y*E/E′ rewrite pop∘push y a = E′/E (⊖₁ 𝐸) ᵇ│• (push *ᵇᶜ⌣) 𝐹′
   /-preserves-⌣ (E ᵇ│ᵇ F) (E′ ᵇ│ᵥ 𝐹) (𝐸 │ᵥᵇ F′) = E′/E (⊖₁ 𝐸) ᵇ│ᵥ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣ {a′⌣a″ = ᵇ∇ᵇ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣ {a′⌣a″ = ᵛ∇ᵛ} (E ᵇ│ᵇ F) (P │ᵇᵇ 𝐹) (.E ᵇ│ᵇ F′) = _ │ᵇᵇ (push *ᵇᵇ⌣) 𝐹
   /-preserves-⌣ (E ᵇ│ᵇ F) (P │ᵇᶜ 𝐹) (.E ᵇ│ᶜ F′) = _ │ᵇᶜ (push *ᵇᶜ⌣) 𝐹
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
