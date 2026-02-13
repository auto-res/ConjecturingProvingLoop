

theorem isOpen_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hxCl : x ∈ closure A := subset_closure hxA
  have hInt : interior (closure A) = closure A := h_open.interior_eq
  simpa [hInt] using hxCl