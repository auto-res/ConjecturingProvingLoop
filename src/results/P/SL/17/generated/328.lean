

theorem Topology.P1_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : Topology.P1 (closure (closure A)) := by
  -- First, obtain `P1` for `closure A` from the existing lemma.
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Rewrite `closure (closure A)` as `closure A` and conclude.
  simpa [closure_closure] using hP1_closure