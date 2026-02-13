

theorem Topology.closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  simpa [Topology.interior_inter_eq_inter_interior (X := X) (A := A) (B := B)]