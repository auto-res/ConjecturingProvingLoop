

theorem Topology.closure_subset_iff_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A : Set X) ⊆ B ↔ A ⊆ B := by
  constructor
  · intro hSub x hxA
    have : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub this
  · intro hSub
    have : closure (A : Set X) ⊆ closure B := closure_mono hSub
    simpa [hB.closure_eq] using this