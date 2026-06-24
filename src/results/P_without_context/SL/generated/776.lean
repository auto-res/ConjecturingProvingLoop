

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hA
  dsimp [Topology.P2, Topology.P1] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hx'