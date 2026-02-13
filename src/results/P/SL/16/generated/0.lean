

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2 x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hsubset hx