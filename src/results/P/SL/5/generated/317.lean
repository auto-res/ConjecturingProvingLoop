

theorem closure_eq_closure_interior_union_closure_diff
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) =
      closure (interior A) ∪ closure (A \ interior A) := by
  classical
  ext x
  constructor
  · intro hxClA
    by_cases hClInt : x ∈ closure (interior A)
    · exact Or.inl hClInt
    · -- Put `x` in the complement of `closure (interior A)`.
      have hxW : x ∈ (closure (interior (A : Set X)))ᶜ := by
        simpa [Set.mem_compl] using hClInt
      -- Show `x ∈ closure (A \ interior A)`.
      have hxClDiff : x ∈ closure (A \ interior A : Set X) := by
        -- Use the neighbourhood characterisation of the closure.
        refine (mem_closure_iff).2 ?_
        intro U hUopen hxU
        -- Intersect with the open set `W` that avoids `interior A`.
        let W : Set X := (closure (interior (A : Set X)))ᶜ
        have hWopen : IsOpen W := isClosed_closure.isOpen_compl
        have hxW' : x ∈ W := hxW
        let V : Set X := U ∩ W
        have hVopen : IsOpen V := hUopen.inter hWopen
        have hxV : x ∈ V := by
          exact And.intro hxU hxW'
        -- Since `x ∈ closure A`, `V` meets `A`.
        have hNon : ((V : Set X) ∩ (A : Set X)).Nonempty := by
          have := (mem_closure_iff).1 hxClA V hVopen hxV
          simpa [V, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
        -- Extract a point `y` in `V ∩ A`; it cannot lie in `interior A`.
        rcases hNon with ⟨y, ⟨⟨hyU, hyW⟩, hyA⟩⟩
        have hyNotInt : y ∈ (interior (A : Set X))ᶜ := by
          intro hyInt
          have : y ∈ closure (interior (A : Set X)) := subset_closure hyInt
          exact hyW this
        have hyDiff : y ∈ A \ interior A := ⟨hyA, hyNotInt⟩
        exact ⟨y, ⟨hyU, hyDiff⟩⟩
      exact Or.inr hxClDiff
  · intro hx
    cases hx with
    | inl hxInt =>
        have hsubset : closure (interior A) ⊆ closure (A : Set X) :=
          Topology.closure_interior_subset_closure (X := X) A
        exact hsubset hxInt
    | inr hxDiff =>
        have hsubset :
            closure (A \ interior A : Set X) ⊆ closure (A : Set X) :=
          closure_mono (Set.diff_subset : (A \ interior A : Set X) ⊆ A)
        exact hsubset hxDiff