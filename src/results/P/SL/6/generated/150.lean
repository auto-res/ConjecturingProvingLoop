

theorem P3_and_interior_closure_empty_implies_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      interior (closure (A : Set X)) = ∅ → A = ∅ := by
  intro hP3 hIntEmpty
  apply Set.Subset.antisymm
  · intro x hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hIntEmpty] using this
  · simpa using (Set.empty_subset (A := A))