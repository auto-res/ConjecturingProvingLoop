

theorem P2_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    A ⊆ closure A := by
  intro x hxA
  -- From `P2`, we have `x ∈ interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The interior is contained in the closure of the same set.
  have hIntSubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  have hxClInt : x ∈ closure (interior A) := hIntSubset hxInt
  -- Finally, `closure (interior A)` is contained in `closure A`.
  have hClSubset : closure (interior A) ⊆ closure A :=
    closure_interior_subset_closure (X := X) (A := A)
  exact hClSubset hxClInt