

theorem Topology.closure_iUnion_interior_subset_closure_interior_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (interior (A i)) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  intro x hx
  -- Choose an index `i` such that `x ∈ closure (interior (A i))`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- The inclusion `A i ⊆ ⋃ j, A j` lifts to interiors via monotonicity.
  have h_int :
      (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
    have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_subset
  -- Taking closures preserves this inclusion.
  have h_closure :
      closure (interior (A i) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int
  -- Conclude that `x ∈ closure (interior (⋃ j, A j))`.
  exact h_closure hx_i