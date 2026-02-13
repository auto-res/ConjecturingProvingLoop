

theorem Topology.denseInterior_iff_interior_closure_interior_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  constructor
  ·
    intro hDense
    exact
      Topology.denseInterior_implies_interior_closure_interior_eq_univ
        (X := X) (A := A) hDense
  ·
    intro hIntEq
    -- Show that `closure (interior A)` equals the whole space.
    have h_closure :
        closure (interior (A : Set X)) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      ·
        intro x _
        -- Since `interior (closure (interior A)) = univ`, every `x`
        -- lies in this interior, hence in the corresponding closure.
        have hx_int :
            (x : X) ∈ interior (closure (interior (A : Set X))) := by
          simpa [hIntEq]
        exact
          (interior_subset :
            interior (closure (interior (A : Set X))) ⊆
              closure (interior (A : Set X))) hx_int
    -- Conclude density from the closure equality.
    simpa [Dense, h_closure]