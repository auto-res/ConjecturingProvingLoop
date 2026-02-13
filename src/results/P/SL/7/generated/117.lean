

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2cl
  -- From `P2 (closure A)` and closedness of `closure A`, we get that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := (Topology.P2_closure_iff_isOpen (A := A))
    exact (hEquiv).1 hP2cl
  -- Openness of `closure A` yields `P3 A`.
  exact Topology.P3_of_open_closure (A := A) hOpen