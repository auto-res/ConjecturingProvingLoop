

theorem Topology.closure_subset_iff_subset_of_isClosed' {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A : Set X) ⊆ B ↔ A ⊆ B := by
  constructor
  · intro hSub x hxA
    exact hSub (subset_closure hxA)
  · intro hSub
    have h : closure (A : Set X) ⊆ closure B := closure_mono hSub
    simpa [hB.closure_eq] using h