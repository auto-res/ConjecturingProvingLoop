

theorem interior_closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior (closure A))) ⊆
      interior (closure (interior (closure B))) := by
  -- First, `closure A ⊆ closure B` by monotonicity of `closure`.
  have h₁ : closure (A : Set X) ⊆ closure B :=
    closure_mono hAB
  -- Taking `interior` on both sides yields
  -- `interior (closure A) ⊆ interior (closure B)`.
  have h₂ :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Applying `closure` again preserves this inclusion.
  have h₃ :
      closure (interior (closure (A : Set X))) ⊆
        closure (interior (closure B)) :=
    closure_mono h₂
  -- Finally, taking `interior` gives the desired result.
  exact interior_mono h₃