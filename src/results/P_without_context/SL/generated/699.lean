

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  calc
    A ⊆ interior (closure (interior A)) := hP2
    _ ⊆ interior (closure A) := by
      exact interior_mono
        (by
          simpa using closure_mono (interior_subset : interior A ⊆ A))