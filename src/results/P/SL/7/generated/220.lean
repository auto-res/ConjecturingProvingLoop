

theorem Topology.closureInterior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    · intro x hx
      cases hx
  · intro hInt
    simpa [hInt] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))