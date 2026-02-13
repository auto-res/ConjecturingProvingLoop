

theorem P1_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  apply le_antisymm
  ·
    exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  ·
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have hclosure : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using hclosure