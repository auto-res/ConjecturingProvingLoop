

theorem Topology.closure_interior_union_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B)) := by
  -- First, establish the basic inclusion on the non-closed level.
  have h_subset :
      (interior (A : Set X) ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        exact
          (Topology.interior_subset_interior_union_left
            (X := X) (A := A) (B := B)) hA
    | inr hB =>
        exact
          (Topology.interior_subset_interior_union_right
            (X := X) (A := A) (B := B)) hB
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset