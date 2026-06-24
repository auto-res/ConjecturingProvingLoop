

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2
  exact fun x hxA =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
      (hP2 hxA)