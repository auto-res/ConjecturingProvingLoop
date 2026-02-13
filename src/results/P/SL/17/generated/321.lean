

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 A := by
  -- `IsOpen (closure A)` is equivalent to `P3 (closure A)`.
  have hP3_closure : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).mpr hOpen
  -- Transfer the `P3` property from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (A := A) hP3_closure