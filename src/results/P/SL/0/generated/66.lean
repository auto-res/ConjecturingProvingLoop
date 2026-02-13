

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2_cl
  -- From `P2` for `closure A` we deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv :=
      (Topology.P2_closure_iff_isOpen_closure (X := X) (A := A))
    exact (hEquiv).1 hP2_cl
  -- An open `closure A` directly yields `P3` for `A`.
  exact (Topology.P3_of_isOpen_closure (X := X) (A := A)) hOpen