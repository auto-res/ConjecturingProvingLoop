

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → Topology.P2 A := by
  intro hOpen
  intro x hxA
  have hsubset : (A : Set X) ⊆ interior (closure A) := by
    have hcl : (A : Set X) ⊆ closure A := subset_closure
    exact interior_maximal hcl hOpen
  have hx' : x ∈ interior (closure A) := hsubset hxA
  simpa [hOpen.interior_eq] using hx'