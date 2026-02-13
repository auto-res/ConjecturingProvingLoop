

theorem P3_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    A ⊆ closure (interior (closure A)) := by
  dsimp [Topology.P3] at hP3
  intro x hxA
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hxInt