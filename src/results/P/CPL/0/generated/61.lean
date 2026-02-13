

theorem P1_closure_interior_any {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  -- First, note that `interior A ⊆ interior (closure (interior A))`.
  have h :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have :
        interior (interior (A : Set X)) ⊆
          interior (closure (interior A)) :=
      interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using this
  -- Take closures and use monotonicity to obtain the required inclusion.
  exact fun x hx => (closure_mono h) hx