

theorem Topology.P2_implies_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → interior A = (∅ : Set X) → A = (∅ : Set X) := by
  intro hP2 hIntEq
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_implies_eq_empty_of_empty_interior (A := A) hP1 hIntEq