

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := interior A) := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    have hsubset : interior A ⊆ closure (interior A) := subset_closure
    have hx_int : x ∈ interior (interior A) := by
      simpa [interior_interior] using hx
    exact (interior_mono hsubset) hx_int
  simpa [interior_interior] using hx'