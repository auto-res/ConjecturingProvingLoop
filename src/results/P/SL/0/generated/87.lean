

theorem P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP2_cl
  -- From `P2` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2_cl
  -- Every open set, in particular `closure A`, satisfies `P1`.
  exact (Topology.isOpen_implies_P1 (X := X) (A := closure (A : Set X))) hOpen