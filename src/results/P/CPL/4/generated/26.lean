

theorem P3_of_closure_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : (x : X) ∈ closure A := subset_closure hx
  simpa [h.interior_eq] using this

theorem P1_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : frontier A ⊆ closure (interior A) := by
  -- Take an arbitrary point of the frontier
  intro x hx
  -- From `P1` we know the two closures coincide
  have hEq : (closure A : Set X) = closure (interior A) := by
    simpa using
      (Eq.symm
        ((P1_iff_closure_interior_eq_closure (X := X) (A := A)).1 hA))
  -- `x` is in `closure A`, hence (using the equality) in `closure (interior A)`
  have hx_closureInt : x ∈ closure (interior A) := by
    have hx_closureA : x ∈ closure A := hx.1
    simpa [hEq] using hx_closureA
  exact hx_closureInt

theorem P1_superset_exists_open {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ A ⊆ closure U := by
  intro hP1
  exact ⟨interior A, isOpen_interior, hP1⟩