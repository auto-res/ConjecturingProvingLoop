

theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- The set difference `A \ B` is clearly a subset of `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply the monotonicity of `interior ∘ closure`.
  exact Topology.interior_closure_mono (A := A \ B) (B := A) hsubset