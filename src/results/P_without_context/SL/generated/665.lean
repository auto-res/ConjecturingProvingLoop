

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2 x hxA
  have : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) this