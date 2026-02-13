

theorem iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    (⋃ i, interior (S i) : Set X) ⊆ interior (⋃ i, S i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
  -- `S i ⊆ ⋃ j, S j`
  have hSub : (S i : Set X) ⊆ ⋃ j, S j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` lifts the inclusion.
  have hIntSub : interior (S i) ⊆ interior (⋃ j, S j) :=
    interior_mono hSub
  exact hIntSub hx_int