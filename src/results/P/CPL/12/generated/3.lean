

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    simpa using
      interior_mono (subset_closure : interior A ⊆ closure (interior A))
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx