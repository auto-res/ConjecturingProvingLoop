

theorem P2_subsingleton {X} [TopologicalSpace X] {A : Set X} [Subsingleton X] : P2 A := by
  intro x hxA
  -- In a subsingleton, any non-empty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro y hy
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hxA
  -- Rewriting shows the desired interior is the whole space.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_subsingleton {X} [TopologicalSpace X] {A : Set X} [Subsingleton X] : P3 A := by
  simpa using (P3_of_P2 (A := A) P2_subsingleton)

theorem P1_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P1 A := by
  intro x hx
  have hclosure : (closure (interior A) : Set X) = Set.univ := by
    simpa [h, closure_univ]
  simpa [hclosure] using (Set.mem_univ x)

theorem P2_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P2 A := by
  intro x hxA
  have h_closure : (closure (interior A) : Set X) = Set.univ := by
    simpa [h, closure_univ]
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  simpa [h_int]

theorem P3_of_interior_eq_univ {X} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A := by
  have hclosure : closure (interior A) = (Set.univ : Set X) := by
    simpa [h, closure_univ]
  exact P3_of_dense_interior (A := A) hclosure