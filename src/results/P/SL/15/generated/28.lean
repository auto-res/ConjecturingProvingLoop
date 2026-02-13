

theorem P1_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  simpa [h_closure_eq]