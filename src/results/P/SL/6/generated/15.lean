

theorem closure_open_satisfies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 A := by
  dsimp [Topology.P3]
  have hInt_eq : interior (closure (A : Set X)) = closure A := hOpen.interior_eq
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [hInt_eq] using hSub