

theorem P2_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have h_closure_eq : closure A = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hP2
  simpa [h_closure_eq]