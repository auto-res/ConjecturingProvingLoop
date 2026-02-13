

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A) ∪ closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  exact interior_mono
    (Topology.closure_interior_union_subset (X := X) (A := A) (B := B))