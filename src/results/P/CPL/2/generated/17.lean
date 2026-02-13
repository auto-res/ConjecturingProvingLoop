

theorem P3_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Set ι} {A : ι → Set X} (hA : ∀ i, i ∈ s → Topology.P3 (X:=X) (A i)) : Topology.P3 (X:=X) (⋃ i, ⋃ (_ : i ∈ s), A i) := by
  classical
  -- Step 1: obtain `P3` for every index contained in `s`
  have h_subtype : ∀ z : {i // i ∈ s}, Topology.P3 (X := X) (A z.1) := by
    intro z
    exact hA z.1 z.2
  -- Step 2: apply `P3_Union` to this family
  have hP3_sub :
      Topology.P3 (X := X) (⋃ z : {i // i ∈ s}, A z.1) := by
    simpa using
      (Topology.P3_Union (X := X)
          (A := fun z : {i // i ∈ s} => A z.1) h_subtype)
  -- Step 3: identify the two unions
  have h_eq :
      (⋃ z : {i // i ∈ s}, A z.1) = ⋃ i, ⋃ (_ : i ∈ s), A i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨z, hxz⟩
      rcases z with ⟨i, hi⟩
      exact
        (Set.mem_iUnion.2
          ⟨i, Set.mem_iUnion.2 ⟨hi, by simpa using hxz⟩⟩)
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx₁⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨hi, hxi⟩
      exact
        (Set.mem_iUnion.2
          ⟨⟨i, hi⟩, by simpa using hxi⟩)
  -- Step 4: rewrite and conclude
  simpa [h_eq] using hP3_sub