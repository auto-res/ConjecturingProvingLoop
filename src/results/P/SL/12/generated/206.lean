

theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- From `P1` we have `closure A = closure (interior A)`.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Now show the required inclusion.
  intro x hx
  -- `x` lies in `closure A` because interiors are contained in the set itself.
  have hx_cl : x ∈ closure (A : Set X) :=
    (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hx
  -- Rewrite with the equality of closures obtained from `P1`.
  simpa [h_eq] using hx_cl