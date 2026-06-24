

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    P2 A → P1 A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset (s := closure (interior A))
  exact Set.Subset.trans h h'