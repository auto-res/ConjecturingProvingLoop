

theorem Topology.P1_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P1 (closure A) := by
  intro hP2
  -- From `P2 (closure A)` we get that `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    (Topology.P2_closure_iff_isOpen_closure (A := A)).1 hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := closure A) hOpen