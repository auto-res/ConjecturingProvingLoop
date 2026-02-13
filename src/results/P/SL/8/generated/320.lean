

theorem interior_iUnion_subset_interior_iUnion {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxIntAi⟩
  have h_sub : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_int : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_sub
  exact h_int hxIntAi