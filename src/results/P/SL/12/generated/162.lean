

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  exact
    Topology.interior_closure_mono
      (X := X) (A := A) (B := A ∪ B)
      (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)