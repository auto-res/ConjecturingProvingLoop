

theorem Topology.P1_of_subset_within_closureInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 (X := X) A) (hAB : (A : Set X) ⊆ B)
    (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 (X := X) B := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxB
  -- Step 1: place `x` in `closure (interior A)` using `hBsubset`.
  have hx_clA : (x : X) ∈ closure (interior A) := hBsubset hxB
  -- Step 2: upgrade to `closure (interior B)` via monotonicity.
  have h_int_subset : interior A ⊆ interior B :=
    interior_mono hAB
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_clA