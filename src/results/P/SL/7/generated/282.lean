

theorem Topology.P3_of_P2_closure_alt {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2cl
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- From `P2 (closure A)` and closedness we deduce that `closure A` is open.
  have hOpenClosure : IsOpen (closure (A : Set X)) :=
    (Topology.P2_closed_iff_isOpen (A := closure (A : Set X)) hClosed).1 hP2cl
  -- Openness of `closure A` gives `P3 (closure A)`.
  have hP3Closure : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen (A := A)).2 hOpenClosure
  -- `P3` transfers from `closure A` to `A` itself.
  exact Topology.P3_of_P3_closure (A := A) hP3Closure