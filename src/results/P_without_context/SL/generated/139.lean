

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact fun x hx => hsubset (hP2 hx)