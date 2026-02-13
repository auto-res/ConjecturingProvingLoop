

theorem P2_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} : (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  intro hF
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (interior (F i))) := (hF i) hxFi
  have hsubset :
      interior (closure (interior (F i)))
        ⊆ interior (closure (interior (⋃ j, F j))) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- take interiors, closures, and interiors again
    have h₂ : interior (F i) ⊆ interior (⋃ j, F j) := interior_mono h₁
    have h₃ :
        closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
      closure_mono h₂
    exact interior_mono h₃
  exact hsubset hxi

theorem P3_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} : (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  intro hF x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (F i)) := (hF i) hxFi
  have hsubset : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- apply monotonicity of closure and interior
    have h₂ : closure (F i) ⊆ closure (⋃ j, F j) := closure_mono h₁
    exact interior_mono h₂
  exact hsubset hxi

theorem open_of_closed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → IsOpen A := by
  intro hClosed hP3
  -- First, show `A ⊆ interior A`.
  have hsubset : (A : Set X) ⊆ interior A := by
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    simpa [hClosed.closure_eq] using hx'
  -- Hence `interior A = A`.
  have hEq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hsubset
  -- Since `interior A` is open, so is `A`.
  have : IsOpen (interior A) := isOpen_interior
  simpa [hEq] using this