

theorem Topology.P1_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P1 (X := X) (A i)) :
    Topology.P1 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Obtain an index witnessing `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- From `P1` for `A i`.
  have hx_cl : x ∈ closure (interior (A i)) := hA i hxAi
  -- Show that this closure is contained in the desired one.
  have h_sub : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors.
    have h_int : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      -- `A i ⊆ ⋃ j, A j`.
      have h_union : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_union
    -- Then, take closures.
    exact closure_mono h_int
  exact h_sub hx_cl