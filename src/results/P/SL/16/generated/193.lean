

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  -- First, any open set satisfies `P1`.
  have hP1A : Topology.P1 (X := X) A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpen
  -- Transport `P1` from `A` to its closure using the existing lemma.
  exact Topology.P1_closure_of_P1 (X := X) (A := A) hP1A