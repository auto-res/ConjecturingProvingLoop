

theorem P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open and `A ⊆ closure A`, we have `A ⊆ interior (closure A)`.
  have hA_subset : (A : Set X) ⊆ interior (closure (A : Set X)) := by
    apply interior_maximal
    · exact subset_closure
    · exact hA
  -- Taking closures preserves this inclusion.
  have h_closure_subset :
      closure (A : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    closure_mono hA_subset
  exact h_closure_subset hx