

theorem Topology.P1_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    A ⊆ closure (interior (closure A)) := by
  intro x hxA
  -- From `P1`, the point `x` lies in `closure (interior A)`.
  have hxClInt : x ∈ closure (interior A) := hP1 hxA
  -- We have `interior A ⊆ interior (closure A)`.
  have hInt : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures preserves inclusions.
  have hCl : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hInt
  -- Combine the facts to conclude.
  exact hCl hxClInt