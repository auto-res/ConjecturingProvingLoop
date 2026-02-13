

theorem closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) =
      closure (interior (A : Set X) ∩ interior B) := by
  apply le_antisymm
  ·
    exact
      Topology.closure_interior_inter_subset_closure_interiors
        (X := X) (A := A) (B := B)
  ·
    exact
      Topology.closure_inter_interior_subset_closure_interior_inter
        (X := X) (A := A) (B := B)