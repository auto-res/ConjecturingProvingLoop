

theorem Topology.interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- Since `A \ B ⊆ A`, apply monotonicity of `interior ∘ closure`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact
    Topology.interior_closure_mono
      (A := A \ B) (B := A) h_subset