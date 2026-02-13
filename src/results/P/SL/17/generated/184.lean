

theorem Topology.closure_interior_diff_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- First, `interior (A \ B) ⊆ interior A` by monotonicity of `interior`.
  have h₁ : interior (A \ B) ⊆ interior A :=
    Topology.interior_diff_subset_interior_left (A := A) (B := B)
  -- Applying `closure_mono` to `h₁` yields the desired inclusion.
  exact closure_mono h₁