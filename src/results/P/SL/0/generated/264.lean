

theorem P2_of_isOpen_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) →
      Topology.P2 (closure (interior (A : Set X))) := by
  intro hOpen
  have hEquiv :=
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A))
  exact (hEquiv).2 hOpen