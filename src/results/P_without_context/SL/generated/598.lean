

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsub : closure (interior A) ⊆ closure A := by
      have hi : interior A ⊆ A := interior_subset
      exact closure_mono hi
    exact interior_mono hsub
  exact hsubset hx'