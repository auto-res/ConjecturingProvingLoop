

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    Topology.P3 A := by
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [Topology.P3, hInt] using hSub