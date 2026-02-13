

theorem Topology.closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  intro x hx
  -- `A \ B` is contained in `A`
  have hSub : (A \ B : Set X) ⊆ A := fun z hz => hz.1
  -- Hence, their interiors satisfy the same inclusion
  have hInt : interior (A \ B) ⊆ interior A := interior_mono hSub
  -- Taking closures preserves inclusion
  have hClos : closure (interior (A \ B)) ⊆ closure (interior A) :=
    closure_mono hInt
  exact hClos hx