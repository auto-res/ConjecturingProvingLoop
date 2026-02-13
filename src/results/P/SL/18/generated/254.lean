

theorem P3_closure_interior_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (closure (interior (A : Set X))) := by
  -- `closure (interior A)` is closed by definition.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- For a closed set, `P3` is equivalent to openness.
  have hEquiv :
      Topology.P3 (closure (interior (A : Set X))) ↔
        IsOpen (closure (interior (A : Set X))) :=
    Topology.P3_closed_iff_open
      (A := closure (interior (A : Set X))) hClosed
  exact (hEquiv.mpr hOpen)