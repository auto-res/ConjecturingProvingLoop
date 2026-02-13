

theorem P1_prod {X Y} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (A ×ˢ B) := by
  intro hA hB
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Membership in the relevant closures for each component
  have h1 : p.1 ∈ closure (interior A) := hA hpA
  have h2 : p.2 ∈ closure (interior B) := hB hpB
  have h_mem : p ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨h1, h2⟩
  ----------------------------------------------------------------
  -- Show that the product of these closures is contained in the
  -- target closure.
  ----------------------------------------------------------------
  -- Step 1: `interior A × interior B ⊆ interior (A × B)`
  have h_int_prod_subset :
      interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
    have h_sub : interior A ×ˢ interior B ⊆ A ×ˢ B := by
      intro q hq
      exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open : IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior).prod isOpen_interior
    exact interior_maximal h_sub h_open
  -- Step 2: take closures
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_prod_subset
  -- Step 3: identify the left-hand closure via `closure_prod_eq`
  have h_prod_closure_eq :
      closure (interior A ×ˢ interior B) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using closure_prod_eq (s := interior A) (t := interior B)
  -- Step 4: collect the inclusions
  have h_sub :
      closure (interior A) ×ˢ closure (interior B) ⊆
        closure (interior (A ×ˢ B)) := by
    simpa [h_prod_closure_eq] using h_closure_subset
  ----------------------------------------------------------------
  -- Final step: apply the inclusion to the point `p`.
  ----------------------------------------------------------------
  exact h_sub h_mem

theorem P2_iff_P3_of_open {X} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _hP3
    exact P2_of_open hA

theorem exists_maximal_P1_subset {X} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B ∧ (∀ C, C ⊆ A → P1 C → C ⊆ B) := by
  classical
  -- Define the family of all `P1` subsets of `A`.
  let ℱ : Set (Set X) := {C | C ⊆ A ∧ P1 C}
  refine ⟨⋃₀ ℱ, ?_, ?_, ?_⟩
  · -- `⋃₀ ℱ ⊆ A`
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCℱ, hxC⟩
    exact (hCℱ.1) hxC
  · -- `P1 (⋃₀ ℱ)`
    have hP1 : P1 (⋃₀ ℱ) := by
      have hAll : ∀ C, C ∈ ℱ → P1 C := by
        intro C hC
        exact hC.2
      exact P1_sUnion (ℱ := ℱ) hAll
    exact hP1
  · -- Maximality
    intro C hCsub hP1C
    have hCmem : C ∈ ℱ := ⟨hCsub, hP1C⟩
    intro x hx
    exact Set.mem_sUnion.2 ⟨C, hCmem, hx⟩