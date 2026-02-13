

theorem P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3_cl
  -- From `P3` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv :=
      (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
    exact (hEquiv).1 hP3_cl
  -- Every open set, in particular `closure A`, satisfies `P2`.
  exact (Topology.isOpen_implies_P2 (X := X) (A := closure (A : Set X))) hOpen