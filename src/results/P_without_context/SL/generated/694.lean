

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  have hIncl : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hClosure : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hClosure
  intro x hx
  exact hIncl (hP2 hx)