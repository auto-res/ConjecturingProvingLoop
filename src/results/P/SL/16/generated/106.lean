

theorem Topology.isOpen_closure_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]
  intro x hx_cl
  -- First, `A` is an open subset of `closure A`, hence contained in its interior.
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hOpen
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl