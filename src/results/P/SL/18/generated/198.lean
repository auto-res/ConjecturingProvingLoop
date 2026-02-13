

theorem P2_closure_interior_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (closure (interior (A : Set X))) := by
  have hEquiv :
      Topology.P2 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P2_closure_interior_iff_open_closure_interior (A := A)
  exact (hEquiv.mpr hOpen)