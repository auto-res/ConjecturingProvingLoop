

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have hInt :
      interior A ⊆ interior (closure (interior A)) :=
    interior_subset_interior_closure_interior (X := X) (A := A)
  -- Taking closures preserves this inclusion
  have hClosure :
      closure (interior A) ⊆
        closure (interior (closure (interior A))) :=
    closure_mono hInt
  exact hClosure hx