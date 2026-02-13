

theorem interior_iUnion_subset_interior_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) :
    (⋃ i, interior (f i : Set X)) ⊆ interior (⋃ i, f i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_int⟩
  have h_subset :
      interior (f i : Set X) ⊆ interior (⋃ j, f j : Set X) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  exact h_subset hx_int