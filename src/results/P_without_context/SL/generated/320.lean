

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  have hsubset :
      interior (closure (interior (A : Set X))) ⊆ interior (closure (A : Set X)) := by
    exact interior_mono (closure_mono interior_subset)
  exact fun x hx => hsubset (hP2 hx)