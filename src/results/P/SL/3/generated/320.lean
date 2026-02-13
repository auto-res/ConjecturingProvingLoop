

theorem closure_interior_union_closure_complement {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (A : Set X)) ∪ closure ((Aᶜ) : Set X) =
      (Set.univ : Set X) := by
  classical
  apply Set.Subset.antisymm
  · -- `closure (interior A) ∪ closure (Aᶜ) ⊆ univ`
    intro x _
    exact Set.mem_univ x
  · -- `univ ⊆ closure (interior A) ∪ closure (Aᶜ)`
    intro x _
    by_cases hInt : (x : X) ∈ interior (A : Set X)
    · -- Case `x ∈ interior A`
      have hx : (x : X) ∈ closure (interior (A : Set X)) :=
        subset_closure hInt
      exact Or.inl hx
    · -- Case `x ∉ interior A`
      have hEq :
          closure ((Aᶜ) : Set X) = (interior (A : Set X))ᶜ :=
        closure_compl_eq_complement_interior (A := A)
      have hx : (x : X) ∈ closure ((Aᶜ) : Set X) := by
        have : (x : X) ∈ (interior (A : Set X))ᶜ := hInt
        simpa [hEq] using this
      exact Or.inr hx