

theorem P1_iff_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = ∅) :
    Topology.P1 A ↔ A = ∅ := by
  constructor
  · intro hP1
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hxA
      have hx : x ∈ closure (interior A) := hP1 hxA
      simpa [hInt, closure_empty] using hx
    have hEq : A = (∅ : Set X) := by
      apply Set.Subset.antisymm hSub
      exact Set.empty_subset _
    exact hEq
  · intro hA
    simpa [hA] using (Topology.P1_empty (X := X))