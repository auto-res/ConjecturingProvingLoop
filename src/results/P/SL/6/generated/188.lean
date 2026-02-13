

theorem closure_union_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  exact
    closure_mono
      (Topology.interior_union_subset (A := A) (B := B))