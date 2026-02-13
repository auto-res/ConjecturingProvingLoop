

theorem interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior B)) := by
  -- Lift the inclusion `A ⊆ B` through `interior` and `closure`.
  have h : closure (interior (A : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    exact hAB
  -- Apply monotonicity of `interior`.
  exact interior_mono h