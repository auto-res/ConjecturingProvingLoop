

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
  -- `A i` is contained in `⋃ j, A j`
  have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` yields the desired inclusion.
  have h_mono : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_subset
  exact h_mono hx_int