

theorem P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h := closure_mono hP1
    simpa [closure_closure] using h
  · intro hClosure
    dsimp [Topology.P1]
    exact Set.Subset.trans subset_closure hClosure