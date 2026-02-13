

theorem Topology.P2_iff_frontier_subset_closure_interior_and_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) ↔
      (frontier A ⊆ closure (interior A) ∧ A ⊆ interior (closure A)) := by
  constructor
  · intro hP2
    have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 (A := A) hP2
    have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 (A := A) hP2
    have hFront :
        frontier A ⊆ closure (interior A) :=
      (Topology.P1_iff_frontier_subset_closure_interior (A := A)).1 hP1
    exact And.intro hFront hP3
  · rintro ⟨hFront, hSub⟩
    have hP1 : Topology.P1 (A := A) :=
      (Topology.P1_iff_frontier_subset_closure_interior (A := A)).2 hFront
    have hP3 : Topology.P3 (A := A) := hSub
    exact
      (Topology.P2_iff_P1_and_P3 (A := A)).2
        ⟨hP1, hP3⟩