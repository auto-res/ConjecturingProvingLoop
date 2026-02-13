

theorem subset_inter_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    (A : Set X) ⊆ closure (interior A) ∩ interior (closure (interior A)) := by
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) := interior_subset hxInt
  exact ⟨hxCl, hxInt⟩