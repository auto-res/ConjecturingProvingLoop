

theorem Topology.isClosed_isOpen_implies_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed (A : Set X) → IsOpen A → frontier (A : Set X) = (∅ : Set X) := by
  intro hClosed hOpen
  -- Any open set satisfies `P2`.
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hOpen
  -- Apply the closed‐plus‐`P2` lemma.
  exact Topology.isClosed_P2_implies_frontier_eq_empty (A := A) hClosed hP2