

theorem P1_and_interior_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → interior (A : Set X) = ∅ → A = ∅ := by
  intro hP1 hIntEmpty
  apply Set.Subset.antisymm
  · intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [hIntEmpty, closure_empty] using this
  · simpa using (Set.empty_subset (A := A))