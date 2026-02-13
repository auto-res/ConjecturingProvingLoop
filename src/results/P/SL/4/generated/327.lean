

theorem interior_inter_closure_subset_interior_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A ∩ closure B := by
  intro x hx
  -- `hx` gives `x ∈ A ∩ closure B`.
  have hx_mem : x ∈ A ∩ closure B := interior_subset hx
  -- The second component is immediate.
  have hx_clB : x ∈ closure B := hx_mem.2
  -- To show `x ∈ interior A`, use monotonicity of `interior`.
  have h_sub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
  have hx_intA : x ∈ interior A := (interior_mono h_sub) hx
  exact And.intro hx_intA hx_clB