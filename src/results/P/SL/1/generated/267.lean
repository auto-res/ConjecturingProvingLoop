

theorem Topology.closure_interior_eq_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, upgrade `P2` to `P1` using closedness of `A`.
  have hP1 : Topology.P1 A :=
    Topology.P1_of_P2_of_isClosed (A := A) hA hP2
  -- Apply the existing lemma that establishes the desired equality from `P1`.
  exact Topology.closure_interior_eq_of_isClosed_of_P1 (A := A) hA hP1