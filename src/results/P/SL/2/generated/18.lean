

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have hcl : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal hcl isOpen_interior
  have hx' : x ∈ interior (closure (interior A)) := hsubset hx
  simpa [interior_interior] using hx'