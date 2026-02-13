

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  exact
    (interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))) hx