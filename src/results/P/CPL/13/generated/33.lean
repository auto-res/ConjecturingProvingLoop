

theorem P1_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) : Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` lies in `closure (interior A)` by the hypothesis `hB`.
  have hx_clA : x ∈ closure (interior A) := hB hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have h_int_sub : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have h_cl_sub : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_sub
  -- Therefore, `x` lies in `closure (interior B)`.
  exact h_cl_sub hx_clA