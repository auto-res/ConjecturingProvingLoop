

theorem Topology.closureInteriorClosure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, monotonicity of `closure` gives `closure A ⊆ closure B`.
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  -- Applying monotonicity of `interior` yields the next inclusion.
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  -- Finally, use monotonicity of `closure` once more to reach the goal.
  exact closure_mono h_interior