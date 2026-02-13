

theorem Topology.Subset_interiorClosure_of_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P3 B) :
    (A : Set X) ⊆ interior (closure B) := by
  intro x hxA
  have hxB : (x : X) ∈ B := hAB hxA
  exact hB hxB