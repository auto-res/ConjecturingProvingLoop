

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx
  exact this