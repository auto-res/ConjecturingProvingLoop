

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure A) → Topology.P3 (A := A) := by
  intro hOpen
  dsimp [Topology.P3]
  intro x hxA
  have hxClos : x ∈ closure A := subset_closure hxA
  simpa [hOpen.interior_eq] using hxClos