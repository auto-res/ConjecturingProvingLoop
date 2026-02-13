

theorem Topology.closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B : Set X)) := by
  -- The union of the interiors is contained in the interior of the union.
  have h_subset :
      (interior (A : Set X) ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.interior_union_subset (X := X) (A := A) (B := B)
  -- Taking closures preserves the inclusion.
  exact closure_mono h_subset