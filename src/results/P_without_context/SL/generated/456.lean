

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  intro x hxA
  have hxI : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : closure (interior A) ⊆ closure A := by
    simpa using closure_mono (interior_subset : interior A ⊆ A)
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hsubset
  exact hmono hxI