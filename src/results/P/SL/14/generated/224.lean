

theorem Topology.closure_interiorUnion_subset_closureInterior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior A) ∪ (interior B) : Set X) ⊆
      closure (interior (A ∪ B)) := by
  have h_sub :
      ((interior A) ∪ (interior B) : Set X) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A) (B := B)
  exact closure_mono h_sub