

theorem Topology.interior_closure_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  exact
    Topology.interior_closure_mono
      (X := X) (A := B) (B := A ∪ B)
      (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)