

theorem Topology.closure_union_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- The union of the interiors is contained in the interior of the union.
  have h_subset :
      (interior (A : Set X) ∪ interior B) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset