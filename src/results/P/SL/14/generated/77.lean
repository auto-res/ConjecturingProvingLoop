

theorem Topology.P1_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- First, `x` lies in `closure (interior A)` by assumption.
  have hx_closure_intA : (x : X) ∈ closure (interior A) := hBsubset hxB
  -- Since `interior A ⊆ interior B`, we have
  -- `closure (interior A) ⊆ closure (interior B)`.
  have h_enlarge : closure (interior A) ⊆ closure (interior B) := by
    have h_int_mono : (interior A : Set X) ⊆ interior B :=
      interior_mono hAB
    exact closure_mono h_int_mono
  -- Hence `x` lies in `closure (interior B)`, as required.
  exact h_enlarge hx_closure_intA