

theorem Topology.P2_implies_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ closure (interior A) := by
  intro hP2 x hxA
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact hP1 hxA