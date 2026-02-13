

theorem exists_maximal_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ Topology.P2 B ∧ (∀ C, C ⊆ A → Topology.P2 C → C ⊆ B) := by
  classical
  -- `S` is the collection of `P2` subsets of `A`.
  let S : Set (Set X) := {C | C ⊆ A ∧ P2 C}
  -- We take `B` to be the union of all sets in `S`.
  refine ⟨⋃₀ S, ?_, ?_, ?_⟩
  -- First, `B ⊆ A`.
  · intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCS, hxC⟩
    exact (hCS.1) hxC
  -- Second, `B` satisfies `P2`.
  ·
    have hforall : ∀ C, C ∈ S → P2 C := by
      intro C hC
      exact hC.2
    have hP2B : P2 (⋃₀ S) := P2_sUnion (X := X) (S := S) hforall
    simpa using hP2B
  -- Finally, `B` is maximal among `P2` subsets of `A`.
  · intro C hC_sub hP2C
    intro x hxC
    have hC_in_S : C ∈ S := by
      show C ⊆ A ∧ P2 C
      exact ⟨hC_sub, hP2C⟩
    exact Set.mem_sUnion.2 ⟨C, hC_in_S, hxC⟩

theorem P3_iff_restrict_to_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hDense : Dense A) : Topology.P3 B ↔ Topology.P3 A := by
  -- The closure of a dense set is the whole space.
  have hClA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the closure of `B` is also the whole space, since `A ⊆ B`.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    ·
      have : (closure (A : Set X)) ⊆ closure B := closure_mono hAB
      simpa [hClA] using this
  -- From the two equalities we get the interiors of the closures.
  have hIntA : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClA, interior_univ]
  have hIntB : interior (closure B) = (Set.univ : Set X) := by
    simpa [hClB, interior_univ]
  -- `P3` for `A` follows from density.
  have hP3A : P3 A := by
    intro x hxA
    have : (x : X) ∈ (Set.univ : Set X) := by trivial
    simpa [hIntA] using this
  -- `P3` for `B` is also immediate.
  have hP3B : P3 B := by
    intro x hxB
    have : (x : X) ∈ (Set.univ : Set X) := by trivial
    simpa [hIntB] using this
  -- Conclude the equivalence.
  exact ⟨fun _ => hP3A, fun _ => hP3B⟩