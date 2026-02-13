

theorem Topology.P3_subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hP3 : Topology.P3 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxIntA : x ∈ interior (closure A) := hP3 hxA
  have hMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  exact hMono hxIntA