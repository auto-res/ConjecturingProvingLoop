

theorem isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open, it is contained in the interior of its closure.
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx