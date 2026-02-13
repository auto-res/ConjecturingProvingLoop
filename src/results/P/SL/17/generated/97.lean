

theorem Topology.subset_interior_closure_of_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (closure A)) :
    A ⊆ interior (closure A) := by
  intro x hxA
  -- First, note that `x ∈ closure A`.
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply the `P3` property for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := hP3 hx_closure
  -- Simplify `interior (closure (closure A))` to `interior (closure A)`.
  simpa [closure_closure] using hx_int