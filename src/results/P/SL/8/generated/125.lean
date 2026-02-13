

theorem P2_imp_eq_empty_of_closureInterior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A)
    (hClInt : closure (interior A) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxA
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
    have hx₂ : x ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hx₁
    simpa [hClInt] using hx₂
  · exact Set.empty_subset _