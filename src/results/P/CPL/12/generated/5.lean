

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  have hInt : interior A = A := hA.interior_eq
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  have : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
  simpa [hInt] using this

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P1 A) → P1 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hAll A hA_mem
  have hx' : x ∈ closure (interior A) := hP1A hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) := by
    have hInt : interior A ⊆ interior (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono hAsub
    exact closure_mono hInt
  exact hsubset hx'