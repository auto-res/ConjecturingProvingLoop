

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 A := by
  -- First, translate the openness of `closure A` into `P3 (closure A)`.
  have hP3_closure : Topology.P3 (closure (A : Set X)) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen (A := A))
    exact (hEquiv).2 hOpen
  -- Then use `P3 (closure A)` to obtain `P3 A`.
  exact Topology.P3_of_P3_closure (A := A) hP3_closure