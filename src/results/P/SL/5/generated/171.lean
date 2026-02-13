

theorem P2_interior_empty_implies_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hInt : interior (A : Set X) = (∅ : Set X)) :
    (A : Set X) = (∅ : Set X) := by
  apply le_antisymm
  · intro x hxA
    have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [hInt] using hx
  · exact Set.empty_subset _