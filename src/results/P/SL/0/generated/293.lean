

theorem P3_of_isOpen_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (closure (interior A)) := by
  have hEquiv :=
    Topology.P3_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A)
  exact (hEquiv).2 hOpen