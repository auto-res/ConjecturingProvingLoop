

theorem P2_sUnion_pair {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (⋃₀ ({A, B} : Set (Set X))) := by
  -- Build the required hypothesis for every set in the pair `{A, B}`.
  have h_all : ∀ C : Set X, C ∈ ({A, B} : Set (Set X)) → Topology.P2 C := by
    intro C hC
    -- Membership in `{A, B}` means `C = A` or `C = B`.
    have h_cases : C = A ∨ C = B := by
      -- `{A, B}` is `insert A {B}`; use `mem_insert_iff`.
      have h' : C = A ∨ C ∈ ({B} : Set (Set X)) := (Set.mem_insert_iff).1 hC
      cases h' with
      | inl hEq => exact Or.inl hEq
      | inr hCB =>
          have hEqB : C = B := by
            simpa [Set.mem_singleton_iff] using hCB
          exact Or.inr hEqB
    -- Deduce `P2 C` from the corresponding hypothesis.
    cases h_cases with
    | inl hEq => simpa [hEq] using hA
    | inr hEq => simpa [hEq] using hB
  -- Apply the general `sUnion` theorem using the hypothesis we just built.
  simpa using
    (Topology.P2_sUnion (X := X) (𝒜 := ({A, B} : Set (Set X))) h_all)