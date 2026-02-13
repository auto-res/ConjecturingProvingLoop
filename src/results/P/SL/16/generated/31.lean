

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  have hxClosure : x ∈ closure A := subset_closure hxA
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  simpa [hInt] using hxClosure