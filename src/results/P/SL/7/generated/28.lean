

theorem Topology.P1_iff_closure_eq_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have h₁ : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using h₁
    · exact closure_mono interior_subset
  · intro hEq
    simpa [Topology.P1, hEq] using (subset_closure : (A : Set X) ⊆ closure A)