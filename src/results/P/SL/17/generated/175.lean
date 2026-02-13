

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2closure
  -- First, convert `P2` for the closed set `closure A` to `P3`.
  have hClosed : IsClosed (closure A) := isClosed_closure
  have hP3closure : Topology.P3 (closure A) :=
    (Topology.P2_iff_P3_of_isClosed (A := closure A) hClosed).1 hP2closure
  -- Then, transfer the `P3` property from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (A := A) hP3closure