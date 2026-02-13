

theorem Topology.P3_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply le_antisymm
  ·
    have : closure A ⊆ closure (interior (closure A)) :=
      closure_mono hP3
    simpa using this
  ·
    have : closure (interior (closure A)) ⊆ closure A := by
      have hsubset : interior (closure A) ⊆ closure A := interior_subset
      simpa [closure_closure] using closure_mono hsubset
    simpa using this

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx