

theorem Topology.interiorClosure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)