

theorem closure_iUnion_interior_subset_closure_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    closure (⋃ i, interior (S i) : Set X) ⊆
      closure (interior (⋃ i, S i)) := by
  have hSub :
      (⋃ i, interior (S i) : Set X) ⊆ interior (⋃ i, S i) :=
    iUnion_interior_subset_interior_iUnion (S := S)
  exact closure_mono hSub