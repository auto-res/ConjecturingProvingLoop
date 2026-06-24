

theorem isOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A := by
  unfold Topology.P1
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this