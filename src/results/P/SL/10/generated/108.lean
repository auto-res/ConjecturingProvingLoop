

theorem Topology.closure_iUnion_interior_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (⋃ i, interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
  -- Every `interior (A i)` is contained in `interior (⋃ i, A i)`.
  have h_subset : (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    have h_incl : interior (A i) ⊆ interior (⋃ j, A j) :=
      interior_mono (Set.subset_iUnion (fun j ↦ A j) i)
    exact h_incl hx_int
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset