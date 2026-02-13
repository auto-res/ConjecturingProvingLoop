

theorem subset_inter_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) (hP3 : Topology.P3 (X := X) A) :
    A ⊆ closure (interior A) ∩ interior (closure A) := by
  intro x hxA
  exact ⟨hP1 hxA, hP3 hxA⟩