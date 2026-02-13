

theorem P2_closure_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hP2_cl
  -- Using the closed–open equivalence for `P2`, deduce that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
    exact (hEquiv).1 hP2_cl
  -- Every open set satisfies `P3`.
  exact (Topology.isOpen_implies_P3 (X := X) (A := closure (A : Set X))) hOpen