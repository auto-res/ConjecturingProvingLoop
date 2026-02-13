

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: move from `interior (closure (interior A))` to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (Topology.interior_closure_interior_subset_interior_closure (A := A)) hx
  -- Step 2: every point of `interior (closure A)` lies in `closure (interior (closure A))`.
  exact (subset_closure hx₁)