

theorem boundary_eq_closure_interior_diff_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) \ interior (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) := by
  intro hP1
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxCl, hxNotInt⟩
    have h_sub : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
      closure_subset_closure_interior_of_P1 (A := A) hP1
    exact And.intro (h_sub hxCl) hxNotInt
  · intro x hx
    rcases hx with ⟨hxClInt, hxNotInt⟩
    have h_sub : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_interior_subset_closure (A := A)
    exact And.intro (h_sub hxClInt) hxNotInt