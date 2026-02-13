

theorem Topology.interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  have h_closure_eq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hA
  simpa [h_closure_eq]