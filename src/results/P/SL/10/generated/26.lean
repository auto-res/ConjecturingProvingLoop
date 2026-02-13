

theorem Topology.P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- First, rewrite `hx` using the equality of closures provided by `hP1`.
  have h_cl_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  have hx' : x ∈ closure (interior A) := by
    simpa [h_cl_eq] using hx
  -- Next, use monotonicity to relate the two closures of interiors.
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : A ⊆ closure A)
    exact closure_mono h_int
  exact h_subset hx'