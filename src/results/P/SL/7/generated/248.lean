

theorem Topology.P1_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- From `P3` and closedness we obtain that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) :=
    (Topology.P3_closed_iff_isOpen (A := closure (A : Set X)) hClosed).1 hP3
  -- An open set satisfies `P1`.
  exact Topology.IsOpen_P1 (A := closure (A : Set X)) hOpen