

theorem closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- From `A ⊆ B` we obtain `closure A ⊆ closure B`.
  have h₁ : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Taking interiors preserves this inclusion.
  have h₂ :
      interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h₁
  -- Finally, closures are monotone, giving the desired result.
  exact closure_mono h₂