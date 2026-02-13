

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, apply monotonicity of `closure` to the inclusion `A ⊆ B`.
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  -- Next, use monotonicity of `interior` to relate the interiors.
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  -- Finally, another application of `closure_mono` yields the desired inclusion.
  exact closure_mono h_interior