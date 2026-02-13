

theorem Topology.closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) = closure (interior A ∩ interior B) := by
  simpa [Topology.interior_inter_eq (X := X) (A := A) (B := B)]